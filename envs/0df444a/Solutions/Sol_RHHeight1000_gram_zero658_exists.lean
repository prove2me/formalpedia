-- Prove2me | solution 1 for RHHeight1000.gram_zero658_exists
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-19T16:39:56.032606+00:00
-- url     : https://prove2.me/submissions/1a1b7014-2cc8-489d-98a6-e2e73531b000

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

namespace RHHeight1000.GramZero658
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

noncomputable def p136 :=
@Mathlib.Meta.NormNum.isRat_le_true.{0} Real
  (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField)) Real.linearOrder
  Real.instIsStrictOrderedRing
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
    true 5)
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
    true 5)
  (Int.ofNat 506427) (Int.ofNat 1014087) 500

noncomputable def p137 :=
@Mathlib.Meta.NormNum.isNNRat_nnratCast.{0} Real
  (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))
  (@FloorSemiring.instCharZero.{0} Real Real.semiring Real.partialOrder
    (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing))
  (NNRat.divNat 101285400
    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
      (@OfNat.ofNat.{0} Nat 10 (instOfNatNat 10)) 5))
  506427 500

noncomputable def p138 :=
@Mathlib.Meta.NormNum.isNNRat_divNat 101285400 101285400 506427
  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
    (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
    (@OfNat.ofNat.{0} Nat 10 (instOfNatNat 10)) 5)
  100000 500 (Mathlib.Meta.NormNum.IsNat.raw_refl 101285400)

noncomputable def p139 :=
@Mathlib.Meta.NormNum.isNNRat_div.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield)
  (@Nat.cast.{0} NNRat
    (@AddMonoidWithOne.toNatCast.{0} NNRat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat
          (@Semiring.toNonAssocSemiring.{0} NNRat
            (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))))))
    101285400)
  (@Nat.cast.{0} NNRat
    (@AddMonoidWithOne.toNatCast.{0} NNRat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat
          (@Semiring.toNonAssocSemiring.{0} NNRat
            (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))))))
    100000)

noncomputable def p140 :=
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
    101285400)
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

noncomputable def p141 :=
@Mathlib.Meta.NormNum.IsNat.to_isNNRat.{0} NNRat
  (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))
  (@Nat.cast.{0} NNRat
    (@AddMonoidWithOne.toNatCast.{0} NNRat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat
          (@Semiring.toNonAssocSemiring.{0} NNRat
            (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))))))
    101285400)
  101285400

noncomputable def p142 :=
p141
  (@Mathlib.Meta.NormNum.isNat_natCast.{0} NNRat
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat
        (@Semiring.toNonAssocSemiring.{0} NNRat
          (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield)))))
    101285400 101285400 (Mathlib.Meta.NormNum.IsNat.raw_refl 101285400))

noncomputable def p143 :=
@p140 101285400 1 506427 1 100000 500
  200
  (@Eq.refl.{1} (NNRat → NNRat → NNRat)
    (@HMul.hMul.{0, 0, 0} NNRat NNRat NNRat
      (@instHMul.{0} NNRat
        (@Distrib.toMul.{0} NNRat
          (@instDistribOfSemiring.{0} NNRat
            (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield)))))))
  p142 (@p9 1 p11)

noncomputable def p144 :=
@p136 1000
  (@Mathlib.Meta.NormNum.IsNNRat.to_isRat.{0} Real
    (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
      true 5)
    506427 500
    (@Mathlib.Meta.NormNum.isNNRat_ofScientific_of_true.{0} Real
      (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)) 101285400
      5 506427 500
      (p137
        (p138 p4
          (@p139 506427 500
            (p143 (@Eq.refl.{1} Nat (Nat.mul 101285400 1))
              (@Eq.refl.{1} Nat 100000)))))))

noncomputable def p145 :=
@Mathlib.Meta.NormNum.isNNRat_nnratCast.{0} Real
  (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))
  (@FloorSemiring.instCharZero.{0} Real Real.semiring Real.partialOrder
    (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing))
  (NNRat.divNat 101408700
    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
      (@OfNat.ofNat.{0} Nat 10 (instOfNatNat 10)) 5))
  1014087 1000

noncomputable def p146 :=
@Mathlib.Meta.NormNum.isNNRat_divNat 101408700 101408700 1014087
  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
    (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
    (@OfNat.ofNat.{0} Nat 10 (instOfNatNat 10)) 5)
  100000 1000 (Mathlib.Meta.NormNum.IsNat.raw_refl 101408700)

noncomputable def p147 :=
@Mathlib.Meta.NormNum.isNNRat_div.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield)
  (@Nat.cast.{0} NNRat
    (@AddMonoidWithOne.toNatCast.{0} NNRat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat
          (@Semiring.toNonAssocSemiring.{0} NNRat
            (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))))))
    101408700)
  (@Nat.cast.{0} NNRat
    (@AddMonoidWithOne.toNatCast.{0} NNRat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat
          (@Semiring.toNonAssocSemiring.{0} NNRat
            (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))))))
    100000)

noncomputable def p148 :=
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
    101408700)
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

noncomputable def p149 :=
@Mathlib.Meta.NormNum.IsNat.to_isNNRat.{0} NNRat
  (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))
  (@Nat.cast.{0} NNRat
    (@AddMonoidWithOne.toNatCast.{0} NNRat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat
          (@Semiring.toNonAssocSemiring.{0} NNRat
            (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))))))
    101408700)
  101408700

noncomputable def p150 :=
p149
  (@Mathlib.Meta.NormNum.isNat_natCast.{0} NNRat
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat
        (@Semiring.toNonAssocSemiring.{0} NNRat
          (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield)))))
    101408700 101408700 (Mathlib.Meta.NormNum.IsNat.raw_refl 101408700))

noncomputable def p151 :=
@p148 101408700 1 1014087 1 100000 1000
  100
  (@Eq.refl.{1} (NNRat → NNRat → NNRat)
    (@HMul.hMul.{0, 0, 0} NNRat NNRat NNRat
      (@instHMul.{0} NNRat
        (@Distrib.toMul.{0} NNRat
          (@instDistribOfSemiring.{0} NNRat
            (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield)))))))
  p150 (@p9 1 p11)

noncomputable def p152 :=
p144
  (@Mathlib.Meta.NormNum.IsNNRat.to_isRat.{0} Real
    (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
      true 5)
    1014087 1000
    (@Mathlib.Meta.NormNum.isNNRat_ofScientific_of_true.{0} Real
      (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)) 101408700
      5 1014087 1000
      (p145
        (p146 p4
          (@p147 1014087 1000
            (p151 (@Eq.refl.{1} Nat (Nat.mul 101408700 1))
              (@Eq.refl.{1} Nat 100000)))))))

theorem d21 : @LE.le.{0} Real
  (@Preorder.toLE.{0} Real
    (@PartialOrder.toPreorder.{0} Real
      (@SemilatticeInf.toPartialOrder.{0} Real
        (@Lattice.toSemilatticeInf.{0} Real
          (@DistribLattice.toLattice.{0} Real (@instDistribLatticeOfLinearOrder.{0} Real Real.linearOrder))))))
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
    true 5)
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
    true 5) :=
p152 (Eq.refl true)

noncomputable def d22 :=
@NonemptyInterval.mk.{0} Real Real.instLE
  (@Prod.mk.{0, 0} Real Real
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
      true 5)
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
      true 5))
  d21

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

theorem d143 : Enclosure.Real.IsNear Real.pi false 226375608064910080 72057594037927936 1
  1000000000000000 :=
BSN.pi_near_15

theorem d144 : p2306 500000000000000 :=
@p501 1 1000000000000000 884279719003555 140737488355328
  1 500000000000000 (Enclosure.Real.IsNear.const false 2 1)
  d143 (Eq.refl true)

noncomputable def p2311 :=
Enclosure.Real.IsNear
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi))
  false 699970842191 4398046511104

noncomputable def p2312 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
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
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
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
Enclosure.Real.IsNear (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi) false
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
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 4 1)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi))
  false p1068 p1070

noncomputable def p2321 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 4 1)
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi) 4 1
  0 1

noncomputable def p2322 :=
@p2321 p1068 p2316 p1071 p2318
  p1068 p1070 p1071 p1072
  (Enclosure.Real.IsNear.const false 4 1) d147 (Eq.refl true)

theorem d148 : p2320 p1071 p1072 :=
p2322

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

noncomputable def p2329 :=
@p2328 p2318 226375608064910080 72057594037927936 1
  1000000000000000 p1059 p2325 p1062
  p2326 d147 d143

theorem d149 : p2323 p1059 p1061 p1062 p1063 :=
p2327 (p2329 (Eq.refl true)) (Eq.refl true)

noncomputable def p2330 :=
Enclosure.Real.IsNear
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 96 1)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi)))
  false 4641825815

noncomputable def p2331 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 96 1)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi)))
  false 4641825815

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
  (@HPow.hPow.{0, 0, 0} Real Nat Real
    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
    (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)))
    12)
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

noncomputable def p2725 :=
nat_lit 7410693711188236507108543040556026102609279018600996098525285376506440296955904

noncomputable def p2761 :=
nat_lit 29642774844752946028434172162224104410437116074403984394101141506025761187823616

noncomputable def p2767 :=
nat_lit 95780971304118053647396689196894323976171195136475136

noncomputable def p2789 :=
nat_lit 2722258935367507707706996859454145691648

noncomputable def p2793 :=
nat_lit 19342813113834066795298816

noncomputable def p2820 :=
nat_lit 21778071482940061661655974875633165533184

noncomputable def p2846 :=
nat_lit 81165673924322027110400000000000000000000000

noncomputable def p2848 :=
nat_lit 69992023193056381579920071267763883691301421788582797965624659405118495974380029543152421664737722368

noncomputable def p2854 :=
nat_lit 243497021772966081331200000000000000000000000

noncomputable def p2863 :=
nat_lit
  1775650789043641010508695207816569540385605730861858341110199241010197423195744501641372399941234194234170066092175719067958164164066441064014355355829104873268767904920662283604813707431425027656908800

noncomputable def p2866 :=
nat_lit
  62147777616527435367804332273579933913496200580165041938856973435356909811851057557448033997943196798195952313226150167378535745742325437240502437454018670564406876672223179926168479760099875967991808000

noncomputable def p2908 :=
nat_lit 121748510886483040665600000000000000000000000

noncomputable def p2930 :=
nat_lit 374144419156711147060143317175368453031918731001856

noncomputable def p2961 :=
nat_lit 1045811745188289256234780144435200000000000000000000000000000000000000

noncomputable def p2972 :=
nat_lit 348603915062763085411593381478400000000000000000000000000000000000000

noncomputable def p2977 :=
nat_lit 6129982163463555433433388108601236734474956488734408704

noncomputable def p2980 :=
nat_lit 4491727243356387717716544818099340391219200000000000000000000000000000000000000000000000000000

noncomputable def p3054 :=
nat_lit 34603008000000000000000000

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

noncomputable def p3309 :=
nat_lit
  398742754905039677285590796924607271486583206189821038744745882131255386529926344580258287370746658488840849688683942720307200000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p3406 :=
nat_lit 77371252455336267181195264

noncomputable def p3422 :=
nat_lit 1857734846290329600000000

noncomputable def p3486 :=
nat_lit 60874255443241520332800000000000000000000000

noncomputable def p3512 :=
nat_lit
  1015922927471052762435759396547172203252676620832305895968258592893646030241792000000000000000000000000000000000000000000000000000000

noncomputable def p3576 :=
nat_lit 62335237573879316820787200000000

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

noncomputable def p4068 :=
@OfNat.ofNat.{0} Real 500
  (@instOfNatAtLeastTwo.{0} Real 500
    (@AddMonoidWithOne.toNatCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real
            (@DivisionSemiring.toSemiring.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))))))
    (Mathlib.Meta.NormNum.instAtLeastTwo 498))

noncomputable def p4091 :=
@Mathlib.Meta.NormNum.isNNRat_inv_pos.{0} Real
  (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))
  (@FloorSemiring.instCharZero.{0} Real Real.semiring Real.partialOrder
    (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing))
  p4068 499 1
  (@Mathlib.Meta.NormNum.IsNat.to_isNNRat.{0} Real
    (@DivisionSemiring.toSemiring.{0} Real
      (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))
    p4068 500
    (@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
      (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
      p4068 500
      (@Eq.refl.{1} Real
        (@OfNat.ofNat.{0} Real 500
          (@instOfNatAtLeastTwo.{0} Real 500
            (@AddMonoidWithOne.toNatCast.{0} Real
              (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 498))))))

noncomputable def p4975 :=
nat_lit
  104611634502814732955149761294712252538601437545985052382802391920185243899673893228564609500776487616922819744602617719602021359070876583487078400000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p5018 :=
nat_lit 73786976294838206464000000000000000

noncomputable def p5163 :=
nat_lit 842498333348457493583344221469363458551160763204392890034487820288000000000000000000000000000000000000000000000

noncomputable def p5168 :=
nat_lit 89202980794122492566142873090593446023921664000000000000000000000000000000

noncomputable def p5171 :=
nat_lit 9444732965739290427392000000000000000

noncomputable def p5189 :=
nat_lit 16615349947311448411297588253504307200000000000000

noncomputable def p5216 :=
nat_lit 20282409603651670423947251286016000000000000000000000000000000

noncomputable def p5269 :=
nat_lit 31828687130226345097944463881396533766429193651030253916189694521162207808802136034115584

noncomputable def p5277 :=
nat_lit 13164036458569648337239753460458804039861886925068638906788872192

noncomputable def p5295 :=
nat_lit 38685626227668133590597632

noncomputable def p5309 :=
nat_lit 822752278660603021077484591278675252491367932816789931674304512

noncomputable def p5362 :=
nat_lit 1532495540865888858358347027150309183618739122183602176

noncomputable def p5743 :=
nat_lit 286687326998758938951352611912760867599570623646035140467198604923365359511060601008752319138765710819328

noncomputable def p5750 :=
nat_lit 65185151242703554760590262029100101153646988597309960020356494379340201592426774597868716032

noncomputable def p5752 :=
nat_lit
  23882118405196465306111515658041880994736934337288366333138126701632082988236800000000000000000000000000000000000000000000000000000

noncomputable def p5762 :=
nat_lit 47890485652059026823698344598447161988085597568237568

noncomputable def p5764 :=
nat_lit 191647029049872542622572578905571856692019200000000000000000000000000000000000000

noncomputable def p5842 :=
nat_lit
  2234038143357312819892246481456537566336261586400535615207244242201184105517426489566429184000000000000000000000000000000000000000000000000000000

noncomputable def p5875 :=
nat_lit 421249166674228746791672110734681729275580381602196445017243910144

noncomputable def p5877 :=
nat_lit 65190923593865350263759371584636199256281519689763389440000000000000000000000000000000000000000000000

noncomputable def p5882 :=
nat_lit 210624583337114373395836055367340864637790190801098222508621955072

noncomputable def p5884 :=
nat_lit 842872547476238872097090864932670050990306517200981196800000000000000000000000000000000000000

noncomputable def p5892 :=
nat_lit 2528617642428716616291272594798010152970919551602943590400000000000000000000000000000000000000

noncomputable def p5917 :=
nat_lit 680564733841876926926749214863536422912

noncomputable def p5920 :=
nat_lit 267727806768202049596103716975411200000000000000000000000

noncomputable def p5932 :=
nat_lit 4835703278458516698824704

noncomputable def p5940 :=
nat_lit 87112285931760246646623899502532662132736

noncomputable def p5990 :=
nat_lit 25711008708143844408671393477458601640355247900524685364822016000000000

noncomputable def p5994 :=
nat_lit 87112285931760246646623899502532662132736000000

noncomputable def p6020 :=
nat_lit 3213876088517980551083924184682325205044405987565585670602752000000

noncomputable def p6024 :=
nat_lit 217780714829400616616559748756331655331840000

noncomputable def p7279 :=
nat_lit
  53631231719770388398296099992823384509917463282369573510894245774887056120294187907207497192667613710760127432745944203415015531247786279785734596024336384

noncomputable def p7287 :=
nat_lit
  12194330274671844653834364178879555881830461494785043558043581873536608354764709453594945715091765512343073949692994620685343654997219864477696

noncomputable def p7305 :=
nat_lit
  2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578097391210961403571828974157824

noncomputable def p7342 :=
nat_lit 59285549689505892056868344324448208820874232148807968788202283012051522375647232

noncomputable def p7449 :=
nat_lit 8958978968711216842229769122273777112486581988938598139599956403855167484720643781523509973086428463104

noncomputable def p7478 :=
nat_lit 2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376

noncomputable def p7523 :=
nat_lit 2993155353253689176481146537402947624255349848014848

noncomputable def p7541 :=
nat_lit 9671406556917033397649408

noncomputable def p7830 :=
nat_lit 9223372036854775808000000000000000

noncomputable def p7956 :=
nat_lit 32592575621351777380295131014550050576823494298654980010178247189670100796213387298934358016

noncomputable def p7958 :=
nat_lit
  3980353067532744217685252609673646832456155722881394388856354450272013831372800000000000000000000000000000000000000000000000000000

noncomputable def p8122 :=
nat_lit 340282366920938463463374607431768211456

noncomputable def p8250 :=
@HMul.hMul.{0, 0, 0} Real Real Real
  (@instHMul.{0} Real
    (@Distrib.toMul.{0} Real
      (@instDistribOfSemiring.{0} Real
        (@DivisionSemiring.toSemiring.{0} Real
          (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
  (@OfNat.ofNat.{0} Real 500
    (@instOfNatAtLeastTwo.{0} Real 500
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8253 :=
@HMul.hMul.{0, 0, 0} Real Real Real
  (@instHMul.{0} Real (@Distrib.toMul.{0} Real (@instDistribOfSemiring.{0} Real Real.semiring)))
  (@OfNat.ofNat.{0} Real 800
    (@instOfNatAtLeastTwo.{0} Real 800
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))))
      (@Nat.instAtLeastTwoHAddOfNat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) 798
          (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
        (@instNeZeroNatHAdd_1 798 (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))

noncomputable def p8255 :=
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
    (Int.negOfNat 16000))

noncomputable def p8257 :=
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
    16000)

noncomputable def p8289 :=
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
  (p8250 Real.pi)

noncomputable def p8290 :=
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
    500)

noncomputable def p8291 :=
@p8289
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p8290
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p8257
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

noncomputable def p8292 :=
@Mathlib.Tactic.Ring.Common.mul_congr.{0} Real Real.instCommSemiring
  (@OfNat.ofNat.{0} Real 500
    (@instOfNatAtLeastTwo.{0} Real 500
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8293 :=
@p8292
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      500)
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  Real.pi

noncomputable def p8294 :=
@Mathlib.Tactic.Ring.cast_pos.{0} Real Real.instCommSemiring
  (@OfNat.ofNat.{0} Real 500
    (@instOfNatAtLeastTwo.{0} Real 500
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8295 :=
@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
  (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
  (@OfNat.ofNat.{0} Real 500
    (@instOfNatAtLeastTwo.{0} Real 500
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8296 :=
@p8293
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
    p8290
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@p8294 500
    (@p8295 500
      (@Eq.refl.{1} Real
        (@OfNat.ofNat.{0} Real 500
          (@instOfNatAtLeastTwo.{0} Real 500
            (@AddMonoidWithOne.toNatCast.{0} Real
              (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 498))))))

noncomputable def p8297 :=
p8296
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

noncomputable def p8298 :=
@Mathlib.Tactic.Ring.Common.add_mul.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    500)
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
    p8290
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))

noncomputable def p8299 :=
@Mathlib.Tactic.Ring.Common.mul_add.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    500)
  p3777
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  p8290

noncomputable def p8300 :=
@Mathlib.Tactic.Ring.Common.mul_pf_right.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    500)
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1)
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    500)
  Real.pi

noncomputable def p8301 :=
@Mathlib.Meta.NormNum.IsNat.to_raw_eq.{0} Real
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      500)
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      1))
  500

noncomputable def p8302 :=
@Mathlib.Meta.NormNum.isNat_mul.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    500)
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1)
  500 1

noncomputable def p8303 :=
@p8302 500
  (@Eq.refl.{1} (Real → Real → Real)
    (@HMul.hMul.{0, 0, 0} Real Real Real
      (@instHMul.{0} Real
        (@Distrib.toMul.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@Mathlib.Meta.NormNum.IsNat.of_raw.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    500)
  (@Mathlib.Meta.NormNum.IsNat.of_raw.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1)
  (@Eq.refl.{1} Nat 500)

noncomputable def p8304 :=
@p8299
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p8290
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (p8300
    (@Nat.rawCast.{0} Nat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat
          (@Semiring.toNonAssocSemiring.{0} Nat (@CommSemiring.toSemiring.{0} Nat Nat.instCommSemiring))))
      1)
    (@p8301
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p8303))
  (@Mathlib.Tactic.Ring.Common.mul_zero.{0} Real Real.instCommSemiring
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      500))

noncomputable def p8305 :=
@p8298
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p8290
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (p8304
    (@Mathlib.Tactic.Ring.Common.add_pf_add_zero.{0} Real Real.instCommSemiring
      (@HAdd.hAdd.{0, 0, 0} Real Real Real
        (@instHAdd.{0} Real
          (@Distrib.toAdd.{0} Real
            (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
        p8290
        (@OfNat.ofNat.{0} Real 0
          (@Zero.toOfNat0.{0} Real
            (@MulZeroClass.toZero.{0} Real
              (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))))

noncomputable def p8306 :=
p8305
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
      p8290
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))

noncomputable def p8307 :=
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
    p8290
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p8257
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))

noncomputable def p8308 :=
@Mathlib.Tactic.Ring.Common.mul_add.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    32)
  p8290
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  p8257

noncomputable def p8309 :=
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
    500)
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    16000)
  Real.pi

noncomputable def p8310 :=
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
      500))
  16000

noncomputable def p8311 :=
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
    500)
  32 500

noncomputable def p8312 :=
@p8311 16000
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
    500)
  (@Eq.refl.{1} Nat 16000)

noncomputable def p8313 :=
@p8308
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p8257
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (p8309
    (@Nat.rawCast.{0} Nat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat
          (@Semiring.toNonAssocSemiring.{0} Nat (@CommSemiring.toSemiring.{0} Nat Nat.instCommSemiring))))
      1)
    (@p8310
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p8312))
  (@Mathlib.Tactic.Ring.Common.mul_zero.{0} Real Real.instCommSemiring
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      32))

noncomputable def p8314 :=
@p8307
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p8257
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (p8313
    (@Mathlib.Tactic.Ring.Common.add_pf_add_zero.{0} Real Real.instCommSemiring
      (@HAdd.hAdd.{0, 0, 0} Real Real Real
        (@instHAdd.{0} Real
          (@Distrib.toAdd.{0} Real
            (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
        p8257
        (@OfNat.ofNat.{0} Real 0
          (@Zero.toOfNat0.{0} Real
            (@MulZeroClass.toZero.{0} Real
              (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))))

noncomputable def p8315 :=
p8314
  (@Mathlib.Tactic.Ring.Common.zero_mul.{0} Real Real.instCommSemiring
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p8290
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))
  (@Mathlib.Tactic.Ring.Common.add_pf_add_zero.{0} Real Real.instCommSemiring
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p8257
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))

noncomputable def p8317 :=
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
    16000)

noncomputable def p8318 :=
@p3730
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    16000)
  (Int.ofNat 16000) (Int.negOfNat 16000) p3731

noncomputable def p8319 :=
p8318
  (@Mathlib.Meta.NormNum.IsNat.to_isInt.{0} Real
    (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      16000)
    16000
    (@Mathlib.Meta.NormNum.IsNat.of_raw.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      16000))

noncomputable def p8320 :=
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
    16000)
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 16000))
  (@Mathlib.Meta.NormNum.IsInt.to_raw_eq.{0} Real p8317 (Int.negOfNat 16000)
    (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (p8319 (@Eq.refl.{1} Int (Int.negOfNat 16000))))

noncomputable def p8321 :=
@Mathlib.Tactic.Ring.Common.neg_add.{0} Real Real.commRing p8257
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  p8255
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  p8320 (@Mathlib.Tactic.Ring.Common.neg_zero.{0} Real Real.commRing)

noncomputable def p8331 :=
@Mathlib.Tactic.Ring.Common.mul_congr.{0} Real Real.instCommSemiring
  (@OfNat.ofNat.{0} Real 800
    (@instOfNatAtLeastTwo.{0} Real 800
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))))
      (@Nat.instAtLeastTwoHAddOfNat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) 798
          (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
        (@instNeZeroNatHAdd_1 798 (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))

noncomputable def p8332 :=
@p8331
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      800)
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  p3713

noncomputable def p8333 :=
@p8332
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
      (Int.negOfNat 50400))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p8257
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))

noncomputable def p8334 :=
@Mathlib.Tactic.Ring.cast_pos.{0} Real Real.instCommSemiring
  (@OfNat.ofNat.{0} Real 800
    (@instOfNatAtLeastTwo.{0} Real 800
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))))
      (@Nat.instAtLeastTwoHAddOfNat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) 798
          (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
        (@instNeZeroNatHAdd_1 798 (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))

noncomputable def p8335 :=
@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
  (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
  (@OfNat.ofNat.{0} Real 800
    (@instOfNatAtLeastTwo.{0} Real 800
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))))
      (@Nat.instAtLeastTwoHAddOfNat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) 798
          (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
        (@instNeZeroNatHAdd_1 798 (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))

noncomputable def p8336 :=
p8333
  (@p8334 800
    (@p8335 800
      (@Eq.refl.{1} Real
        (@OfNat.ofNat.{0} Real 800
          (@instOfNatAtLeastTwo.{0} Real 800
            (@AddMonoidWithOne.toNatCast.{0} Real
              (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 798))))))

noncomputable def p8337 :=
@Mathlib.Tactic.Ring.Common.add_mul.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    800)
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
      (Int.negOfNat 50400))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p8257
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))

noncomputable def p8338 :=
@Mathlib.Tactic.Ring.Common.mul_add.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    800)
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
    (Int.negOfNat 50400))

noncomputable def p8339 :=
@Mathlib.Meta.NormNum.IsInt.to_raw_eq.{0} Real
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      800)
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 63)))
  (Int.negOfNat 50400)

noncomputable def p8340 :=
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
    800)
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 63))

noncomputable def p8341 :=
@p8340 (Int.ofNat 800) (Int.negOfNat 63) (Int.negOfNat 50400)
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
      800)
    800
    (@Mathlib.Meta.NormNum.IsNat.of_raw.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      800))

noncomputable def p8342 :=
@p8338
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p8257
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 50400))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p8257
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))
  (@p8339 (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (p8341
      (@Mathlib.Meta.NormNum.IsInt.of_raw.{0} Real
        (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)) (Int.negOfNat 63))
      (@Eq.refl.{1} Int (Int.negOfNat 50400))))

noncomputable def p8343 :=
@Mathlib.Tactic.Ring.Common.mul_add.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    800)
  p3819
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  p8257

noncomputable def p8344 :=
@Mathlib.Tactic.Ring.Common.mul_pf_right.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    800)
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    20)
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    16000)
  Real.pi

noncomputable def p8345 :=
@Mathlib.Meta.NormNum.IsNat.to_raw_eq.{0} Real
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      800)
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      20))
  16000

noncomputable def p8346 :=
@Mathlib.Meta.NormNum.isNat_mul.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    800)
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    20)
  800 20

noncomputable def p8347 :=
@p8346 16000
  (@Eq.refl.{1} (Real → Real → Real)
    (@HMul.hMul.{0, 0, 0} Real Real Real
      (@instHMul.{0} Real
        (@Distrib.toMul.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@Mathlib.Meta.NormNum.IsNat.of_raw.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    800)
  (@Mathlib.Meta.NormNum.IsNat.of_raw.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    20)
  (@Eq.refl.{1} Nat 16000)

noncomputable def p8348 :=
@p8343
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p8257
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (p8344
    (@Nat.rawCast.{0} Nat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat
          (@Semiring.toNonAssocSemiring.{0} Nat (@CommSemiring.toSemiring.{0} Nat Nat.instCommSemiring))))
      1)
    (@p8345
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p8347))
  (@Mathlib.Tactic.Ring.Common.mul_zero.{0} Real Real.instCommSemiring
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      800))

noncomputable def p8349 :=
p8342
  (p8348
    (@Mathlib.Tactic.Ring.Common.add_pf_add_zero.{0} Real Real.instCommSemiring
      (@HAdd.hAdd.{0, 0, 0} Real Real Real
        (@instHAdd.{0} Real
          (@Distrib.toAdd.{0} Real
            (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
        p8257
        (@OfNat.ofNat.{0} Real 0
          (@Zero.toOfNat0.{0} Real
            (@MulZeroClass.toZero.{0} Real
              (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))))

noncomputable def p8350 :=
@Mathlib.Tactic.Ring.Common.add_pf_add_lt.{0} Real Real.instCommSemiring
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p8257
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p8257
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 50400))

noncomputable def p8351 :=
p8349
  (p8350
    (@Mathlib.Tactic.Ring.Common.add_pf_zero_add.{0} Real Real.instCommSemiring
      (@HAdd.hAdd.{0, 0, 0} Real Real Real
        (@instHAdd.{0} Real
          (@Distrib.toAdd.{0} Real
            (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
        p8257
        (@OfNat.ofNat.{0} Real 0
          (@Zero.toOfNat0.{0} Real
            (@MulZeroClass.toZero.{0} Real
              (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))))

noncomputable def p8352 :=
@p8337
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 50400))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p8257
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))
  p8351

noncomputable def p8353 :=
p8352
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

noncomputable def p8354 :=
p8353
  (@Mathlib.Tactic.Ring.Common.add_pf_add_zero.{0} Real Real.instCommSemiring
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
        (Int.negOfNat 50400))
      (@HAdd.hAdd.{0, 0, 0} Real Real Real
        (@instHAdd.{0} Real
          (@Distrib.toAdd.{0} Real
            (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
        p8257
        (@OfNat.ofNat.{0} Real 0
          (@Zero.toOfNat0.{0} Real
            (@MulZeroClass.toZero.{0} Real
              (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))))

noncomputable def p8355 :=
@Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@Mathlib.Meta.NormNum.instAddMonoidWithOne.{0} Real
      (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)))
    50400)
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p8255
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 50400))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p8257
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))

noncomputable def p8356 :=
@Mathlib.Meta.NormNum.isInt_add.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@Nat.rawCast.{0} Real
    (@Mathlib.Meta.NormNum.instAddMonoidWithOne.{0} Real
      (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)))
    50400)
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 50400))
  (Int.ofNat 50400) (Int.negOfNat 50400)

noncomputable def p8357 :=
@p8356 (Int.ofNat 0)
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
      50400)
    50400
    (@Mathlib.Meta.NormNum.IsNat.of_raw.{0} Real
      (@Mathlib.Meta.NormNum.instAddMonoidWithOne.{0} Real
        (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)))
      50400))
  (@Mathlib.Meta.NormNum.IsInt.of_raw.{0} Real
    (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)) (Int.negOfNat 50400))

noncomputable def p8358 :=
@Mathlib.Meta.NormNum.IsInt.to_isNat.{0} Real
  (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@Mathlib.Meta.NormNum.instAddMonoidWithOne.{0} Real
        (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)))
      50400)
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 50400)))
  0 (p8357 (@Eq.refl.{1} Int (Int.ofNat 0)))

noncomputable def p8359 :=
@Mathlib.Meta.NormNum.isInt_add.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 16000))
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    16000)
  (Int.negOfNat 16000) (Int.ofNat 16000)

noncomputable def p8360 :=
@p8359 (Int.ofNat 0)
  (@Eq.refl.{1} (Real → Real → Real)
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@Mathlib.Meta.NormNum.IsInt.of_raw.{0} Real
    (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)) (Int.negOfNat 16000))
  (@Mathlib.Meta.NormNum.IsNat.to_isInt.{0} Real
    (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      16000)
    16000
    (@Mathlib.Meta.NormNum.IsNat.of_raw.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      16000))

noncomputable def p8361 :=
@Mathlib.Meta.NormNum.IsInt.to_isNat.{0} Real
  (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 16000))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      16000))
  0 (p8360 (@Eq.refl.{1} Int (Int.ofNat 0)))

noncomputable def p8362 :=
@Mathlib.Tactic.Ring.Common.add_overlap_pf_zero.{0} Real Real.instCommSemiring
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 16000))
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    16000)
  Real.pi
  (@Nat.rawCast.{0} Nat
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat
        (@Semiring.toNonAssocSemiring.{0} Nat (@CommSemiring.toSemiring.{0} Nat Nat.instCommSemiring))))
    1)
  p8361

noncomputable def p8363 :=
@Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero.{0} Real Real.instCommSemiring p8255
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  p8257
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  p8362

noncomputable def p8371 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (@OfNat.ofNat.{0} Real 500
    (@instOfNatAtLeastTwo.{0} Real 500
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8380 :=
@Mathlib.Tactic.CancelDenoms.sub_subst.{0} Real
  (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))
  (@OfNat.ofNat.{0} Real 500
    (@instOfNatAtLeastTwo.{0} Real 500
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8384 :=
@Mathlib.Tactic.CancelDenoms.div_subst.{0} Real Real.instField
  (@OfNat.ofNat.{0} Real 1
    (@One.toOfNat1.{0} Real
      (@AddMonoidWithOne.toOne.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))))
  (@OfNat.ofNat.{0} Real 500
    (@instOfNatAtLeastTwo.{0} Real 500
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8385 :=
@p8384
  (@OfNat.ofNat.{0} Real 500
    (@instOfNatAtLeastTwo.{0} Real 500
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8387 :=
@HDiv.hDiv.{0, 0, 0} Real Real Real
  (@instHDiv.{0} Real
    (@DivInvMonoid.toDiv.{0} Real
      (@DivisionRing.toDivInvMonoid.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))
  (@OfNat.ofNat.{0} Real 500
    (@instOfNatAtLeastTwo.{0} Real 500
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8388 :=
@Mathlib.Meta.NormNum.isNat_eq_true.{0} Real
  (@Mathlib.Meta.NormNum.instAddMonoidWithOne'.{0} Real
    (@DivisionSemiring.toSemiring.{0} Real
      (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))
  (p8387 p4068)
  (@OfNat.ofNat.{0} Real 1
    (@One.toOfNat1.{0} Real
      (@AddMonoidWithOne.toOne.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))))
  1

noncomputable def p8389 :=
@Mathlib.Meta.NormNum.isNNRat_div.{0} Real
  (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))
  (@OfNat.ofNat.{0} Real 500
    (@instOfNatAtLeastTwo.{0} Real 500
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8390 :=
p8250
  (@Inv.inv.{0} Real
    (@InvOneClass.toInv.{0} Real
      (@DivInvOneMonoid.toInvOneClass.{0} Real
        (@DivisionMonoid.toDivInvOneMonoid.{0} Real
          (@GroupWithZero.toDivisionMonoid.{0} Real
            (@DivisionSemiring.toGroupWithZero.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))))))
    p4068)

noncomputable def p8391 :=
@HMul.hMul.{0, 0, 0} Real Real Real
  (@instHMul.{0} Real (@Distrib.toMul.{0} Real (@instDistribOfSemiring.{0} Real Real.semiring)))
  (@OfNat.ofNat.{0} Real 500
    (@instOfNatAtLeastTwo.{0} Real 500
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8392 :=
p8391
  (@Inv.inv.{0} Real
    (@InvOneClass.toInv.{0} Real
      (@DivInvOneMonoid.toInvOneClass.{0} Real
        (@DivisionMonoid.toDivInvOneMonoid.{0} Real
          (@GroupWithZero.toDivisionMonoid.{0} Real
            (@DivisionSemiring.toGroupWithZero.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))))))
    p4068)

noncomputable def p8393 :=
@Mathlib.Meta.NormNum.isNNRat_mul.{0} Real
  (@DivisionSemiring.toSemiring.{0} Real
    (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real (@Distrib.toMul.{0} Real (@instDistribOfSemiring.{0} Real Real.semiring))))
  (@OfNat.ofNat.{0} Real 500
    (@instOfNatAtLeastTwo.{0} Real 500
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8394 :=
@p8393
  (@Inv.inv.{0} Real
    (@InvOneClass.toInv.{0} Real
      (@DivInvOneMonoid.toInvOneClass.{0} Real
        (@DivisionMonoid.toDivInvOneMonoid.{0} Real
          (@GroupWithZero.toDivisionMonoid.{0} Real
            (@DivisionSemiring.toGroupWithZero.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))))))
    p4068)

noncomputable def p8395 :=
@Mathlib.Meta.NormNum.IsNat.to_isNNRat.{0} Real
  (@DivisionSemiring.toSemiring.{0} Real
    (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))
  (@OfNat.ofNat.{0} Real 500
    (@instOfNatAtLeastTwo.{0} Real 500
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8396 :=
@p8394 500 1 1 1 500 1 500
  (@Eq.refl.{1} (Real → Real → Real)
    (@HMul.hMul.{0, 0, 0} Real Real Real
      (@instHMul.{0} Real (@Distrib.toMul.{0} Real (@instDistribOfSemiring.{0} Real Real.semiring)))))
  (@p8395 500
    (@p8295 500
      (@Eq.refl.{1} Real
        (@OfNat.ofNat.{0} Real 500
          (@instOfNatAtLeastTwo.{0} Real 500
            (@AddMonoidWithOne.toNatCast.{0} Real
              (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 498))))))

noncomputable def p8397 :=
@Mathlib.Meta.NormNum.IsNNRat.to_isNat.{0} Real
  (@DivisionSemiring.toSemiring.{0} Real
    (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))
  (p8387 p4068) 1
  (@p8389 p4068 1 1
    (@Mathlib.Meta.NormNum.IsNat.to_isNNRat.{0} Real
      (@DivisionSemiring.toSemiring.{0} Real
        (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))
      p8390 1
      (@Mathlib.Meta.NormNum.IsNNRat.to_isNat.{0} Real
        (@DivisionSemiring.toSemiring.{0} Real
          (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))
        p8392 1
        (p8396 p4091 (@Eq.refl.{1} Nat (Nat.mul 500 1))
          (@Eq.refl.{1} Nat 500)))))

noncomputable def p8398 :=
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
  (@OfNat.ofNat.{0} Real 500
    (@instOfNatAtLeastTwo.{0} Real 500
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8399 :=
@Mathlib.Meta.NormNum.isNat_eq_true.{0} Real
  (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
  p8398
  (@OfNat.ofNat.{0} Real 500
    (@instOfNatAtLeastTwo.{0} Real 500
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8400 :=
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
  (@OfNat.ofNat.{0} Real 500
    (@instOfNatAtLeastTwo.{0} Real 500
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8401 :=
@p8400 1 500 500
  (@Eq.refl.{1} (Real → Real → Real)
    (@HMul.hMul.{0, 0, 0} Real Real Real
      (@instHMul.{0} Real (@Distrib.toMul.{0} Real (@instDistribOfSemiring.{0} Real Real.semiring)))))
  (p3747
    (@Nat.cast_one.{0} Real
      (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))))
  (@p8295 500
    (@Eq.refl.{1} Real
      (@OfNat.ofNat.{0} Real 500
        (@instOfNatAtLeastTwo.{0} Real 500
          (@AddMonoidWithOne.toNatCast.{0} Real
            (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
          (Mathlib.Meta.NormNum.instAtLeastTwo 498)))))
  (@Eq.refl.{1} Nat 500)

noncomputable def p8403 :=
@Mathlib.Tactic.CancelDenoms.mul_subst.{0} Real (@Field.toCommRing.{0} Real Real.instField)
  (@OfNat.ofNat.{0} Real 1
    (@One.toOfNat1.{0} Real
      (@AddMonoidWithOne.toOne.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))))
  (@OfNat.ofNat.{0} Real 500
    (@instOfNatAtLeastTwo.{0} Real 500
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8404 :=
@p8403
  (@OfNat.ofNat.{0} Real 500
    (@instOfNatAtLeastTwo.{0} Real 500
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8405 :=
@p8404
  (@OfNat.ofNat.{0} Real 32
    (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
  Real.pi p3705 (p8250 Real.pi)

noncomputable def p8406 :=
@HMul.hMul.{0, 0, 0} Real Real Real
  (@instHMul.{0} Real
    (@inferInstance.{1} (Mul.{0} Real)
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real
          (@DivisionSemiring.toSemiring.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))))))
  (@OfNat.ofNat.{0} Real 500
    (@instOfNatAtLeastTwo.{0} Real 500
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8407 :=
p8405 (@rfl.{1} Real p3930) (@rfl.{1} Real (p8406 Real.pi))
  (@p8399 500 p8401
    (@p8295 500
      (@Eq.refl.{1} Real
        (@OfNat.ofNat.{0} Real 500
          (@instOfNatAtLeastTwo.{0} Real 500
            (@AddMonoidWithOne.toNatCast.{0} Real
              (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 498))))))

noncomputable def p8411 :=
@Mathlib.Meta.NormNum.isNat_lt_true.{0} Real Real.semiring Real.partialOrder Real.instIsOrderedRing
  (@FloorSemiring.instCharZero.{0} Real (@Ring.toSemiring.{0} Real Real.instRing) Real.partialOrder
    (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing))
  (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
  (@OfNat.ofNat.{0} Real 500
    (@instOfNatAtLeastTwo.{0} Real 500 Real.instNatCast
      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 499 (instOfNatNat 499))
        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 498 (instOfNatNat 498))))))
  0 500
  (@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
    (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
    (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) 0
    (@Nat.cast_zero.{0} Real
      (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))))

noncomputable def p8412 :=
p8411
  (@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
    (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
    (@OfNat.ofNat.{0} Real 500
      (@instOfNatAtLeastTwo.{0} Real 500 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 499 (instOfNatNat 499))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 498 (instOfNatNat 498))))))
    500
    (@Eq.refl.{1} Real
      (@OfNat.ofNat.{0} Real 500
        (@instOfNatAtLeastTwo.{0} Real 500
          (@AddMonoidWithOne.toNatCast.{0} Real
            (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
          (Mathlib.Meta.NormNum.instAtLeastTwo 498)))))

noncomputable def p8413 :=
@Mathlib.Meta.NormNum.isNat_lt_true.{0} Real Real.semiring Real.partialOrder Real.instIsOrderedRing
  (@FloorSemiring.instCharZero.{0} Real (@Ring.toSemiring.{0} Real Real.instRing) Real.partialOrder
    (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing))
  (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
  (@OfNat.ofNat.{0} Real 800
    (@instOfNatAtLeastTwo.{0} Real 800 Real.instNatCast
      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 799 (instOfNatNat 799))
        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 798 (instOfNatNat 798))))))
  0 800
  (@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
    (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
    (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) 0
    (@Nat.cast_zero.{0} Real
      (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))))

noncomputable def p8414 :=
p8413
  (@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
    (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
    (@OfNat.ofNat.{0} Real 800
      (@instOfNatAtLeastTwo.{0} Real 800 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 799 (instOfNatNat 799))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 798 (instOfNatNat 798))))))
    800
    (@Eq.refl.{1} Real
      (@OfNat.ofNat.{0} Real 800
        (@instOfNatAtLeastTwo.{0} Real 800
          (@AddMonoidWithOne.toNatCast.{0} Real
            (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
          (Mathlib.Meta.NormNum.instAtLeastTwo 798)))))

noncomputable def p9181 :=
nat_lit
  8509400989195354199368263656857507193865861929927998419006993725293279654209400021870274696120295805795839062183088527584407485957821021981962249179528438649071163716377865

noncomputable def p9182 :=
nat_lit
  15458150092069033378781407563727949377195709318825739994628941005806076569158241698144775066327690311849854464126008708709460314644171950622971634693868322994787923259293696

noncomputable def p9183 :=
Enclosure.Real.IsNear
  (hardyZApproximantRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
      true 5))
  false p9181 p9182

noncomputable def p9184 :=
nat_lit
  191872010730065501236481132563259428845157200774698306491848149352646868685898673583447803128158197184956959121492799708422615218452899736286264256469428355943531248810353331245669700036631026628942661635311240018814880955391

noncomputable def p9185 :=
nat_lit
  59907139862759266398578887939066098984504820245145639478531086150369368641451050197557446777179453456057664927889508749557437316360385049617228715545067520000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p9186 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZApproximantRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
      true 5))
  (hardyZApproximantRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
      true 5))
  false p9181

noncomputable def p9187 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
  (Zeta.RiemannSiegel.mainSumOfPhase
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
      true 5)
    12)

noncomputable def p9188 :=
@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p9189 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (@HPow.hPow.{0, 0, 0} Real Nat Real
    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
    (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)))
    12)
  (p9188
    (@Neg.neg.{0} Real Real.instNeg
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
        (@OfNat.ofNat.{0} Real 4
          (@instOfNatAtLeastTwo.{0} Real 4 Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))))))

noncomputable def p9190 :=
Real.sqrt
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p9191 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p9189
  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
        (Enclosure.sfrac false 12 1)))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Zeta.RiemannSiegel.correctionLinear
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
          (Enclosure.sfrac false 12 1)))
      (@Inv.inv.{0} Real Real.instInv p9190)))

noncomputable def p9192 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZApproximantRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
      true 5))
  (p9187 p9191) false p9181

noncomputable def p9193 :=
@BSN.floor_sqrt_eq_dec
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
    true 5)
  101285400 100000 12
  (Enclosure.sfrac_ofScientific_eq 101285400 5 100000 (Eq.refl true))

noncomputable def p9194 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (Zeta.RiemannSiegel.mainSumOfPhase
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
      true 5)
    12)

noncomputable def p9195 :=
nat_lit
  1963359040381701767560392345243693359859129245833853716039380395260066057676930723127220349382336192569603300980879772785325214532335588173126152319564498288152254632714999

noncomputable def p9196 :=
nat_lit
  2184092704215829916114534980944980994100322465794693716628522183438306974449156070976120245796057876174848529427564773206586638939640513973456955349428355943531248810353331245669700036631026628942661635311240018814880955391

noncomputable def p9197 :=
nat_lit
  292380791657152765131383650132066876237908870399137574754997942763294752987292494637716116594984068541912768199645404721982592253811364198670599697061419813597624551508037998026424320

noncomputable def p9198 :=
@p9194 p9191 23278418987 34359738368 217591
  68719476736 p9195 p9182 p9196 p9185
  p9197 p9181

noncomputable def p9199 :=
@Enclosure.Real.IsNear.of_eq
  (Zeta.RiemannSiegel.mainSumOfPhase
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
      true 5)
    12)

noncomputable def p9200 :=
@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
      true 5)
    12)

noncomputable def p9201 :=
p9200
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
      true 5)
    12)

noncomputable def p9202 :=
@p9199 p9201 false 23278418987 34359738368 217591
  68719476736
  (BSN.main_sum_of_phase_eq
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
      true 5)
    12)

noncomputable def p9203 :=
@Enclosure.Real.IsNear.addLit_ff
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
      true 5)
    12)

noncomputable def p9204 :=
@p9203
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
      true 5)
    12)

noncomputable def p9205 :=
@p9204 46556837974 137438953472 217591 137438953472
  46556837974 137438953472 217591 137438953472 12797446176224057491456
  23278418987 34359738368

noncomputable def p9206 :=
BSN.mainSumRS_step
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
      true 5))
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
    true 5)
  Real.cos BSN.quadSignNeg

noncomputable def p9207 :=
p9206 11 12 101285400 100000 286
  137438953472 68719476736 2305843009213693952 false 284109910356378
  3356

noncomputable def p9208 :=
p9207 341522969406 43 39675208392 8 false
  82649548187 204039 true 58854762473 7244019458077122842 1

noncomputable def p9209 :=
p9208 false 125028815743 true false 46556837974 217591
  BSN.abs_quadSignNeg (BSN.cos_quad_nat2 286 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 125028815743 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101285400 5 100000 (Eq.refl true))
  (Eq.refl true)

noncomputable def p9210 :=
BSN.mainSumRS_step2
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
      true 5))
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
    true 5)
  Real.cos Real.cos

noncomputable def p9211 :=
p9210 BSN.quadSignPos BSN.quadSignNeg 9 10 11 101285400
  100000 168 230 137438953472 68719476736

noncomputable def p9212 :=
p9211 2305843009213693952 false 284109910356378 3356
  316464885454 43 43462013224 8 329564216814 43
  41439403656

noncomputable def p9213 :=
p9212 8 false 103614007944 175042 true 153529385492
  true 36146147908 7244019458077122842 1 false

noncomputable def p9214 :=
p9213 60241541052 false false 132713108241 true false
  82649548187 204039 BSN.abs_quadSignPos
  (BSN.cos_quad_nat0 168 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 60241541052 137438953472)

noncomputable def p9215 :=
p9210 BSN.quadSignPos BSN.quadSignPos 7 8 9 101285400
  100000 24 100 137438953472 68719476736

noncomputable def p9216 :=
p9215 2305843009213693952 false 284109910356378 3356
  285796269294 43 48592008000 16 301984246446 43
  45812984488

noncomputable def p9217 :=
p9216 8 false 74713242321 142793 true 178657704590
  true 167181266203 7244019458077122842 1 false

noncomputable def p9218 :=
p9217 36777222449 false false 47694161794 false false
  103614007944 175042 BSN.abs_quadSignPos
  (BSN.cos_quad_nat0 24 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 36777222449 137438953472)

noncomputable def p9219 :=
BSN.mainSumRS_step2
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
      true 5))
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
    true 5)
  Real.cos Real.sin

noncomputable def p9220 :=
p9219 BSN.quadSignPos BSN.quadSignNeg 5 6 7 101285400
  100000 160 61 137438953472 68719476736

noncomputable def p9221 :=
p9220 2305843009213693952 false 284109910356378 3356
  246257546308 43 56109217800 8 267443854420 43
  51947041624

noncomputable def p9222 :=
p9221 8 false 68631018720 105893 false 144793024558
  false 59127832049 7244019458077122842 1 false

noncomputable def p9223 :=
p9222 67967019155 false false 57320720128 true false
  74713242321 142793 BSN.abs_quadSignPos
  (BSN.cos_quad_nat0 160 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 67967019155 137438953472)

noncomputable def p9224 :=
p9210 BSN.quadSignNeg BSN.quadSignNeg 3 4 5 101285400
  100000 422 278 137438953472 68719476736

noncomputable def p9225 :=
p9224 2305843009213693952 false 284109910356378 3356
  190530846192 42 68719476728 8 221199462352 42
  61464568544

noncomputable def p9226 :=
p9225 16 false 193640638160 62391 false 24990086493
  false 50118405591 7244019458077122842 1 false

noncomputable def p9227 :=
p9226 135173272087 true false 128401694362 true false
  68631018720 105893 BSN.abs_quadSignNeg
  (BSN.cos_quad_nat2 422 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 135173272087 137438953472)

noncomputable def p9228 :=
BSN.mainSumRS_step2
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
      true 5))
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
    true 5)
  Real.sin Real.sin

noncomputable def p9229 :=
p9228 BSN.quadSignNeg BSN.quadSignPos 1 2 3 101285400
  100000 869 607 137438953472 68719476736

noncomputable def p9230 :=
p9229 2305843009213693952 false 284109910356378 3356
  95265423088 42 97184016000 16 150992123216 42
  79350416784

noncomputable def p9231 :=
p9230 16 false 137438012976 3402 false 12749276330
  false 132552202241 7244019458077122842 1 false

noncomputable def p9232 :=
p9231 12730999586 true false 112938028789 false false
  193640638160 62391 BSN.abs_quadSignNeg
  (BSN.cos_quad_nat1 869 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 12730999586 137438953472)

noncomputable def p9233 :=
@Enclosure.Real.IsNear.recentre'
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
      true 5)
    1)

noncomputable def p9234 :=
@Enclosure.Real.IsNear.of_eq
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
      true 5)
    1)

noncomputable def p9235 :=
@p9234
  (Real.cos
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
        true 5)))
  false 8589875811

noncomputable def p9236 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
        true 5)))
  false 17179751622

noncomputable def p9237 :=
@Enclosure.Real.IsNear.cos_image
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
      true 5))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 35513738794547)
    (@Nat.cast.{0} Real Real.instNatCast 17179869184))
  false 35513738794547

noncomputable def p9238 :=
nat_lit 12563994394936680616330748044917408390569553622215523993

noncomputable def p9239 :=
nat_lit 6077866973743185591873258409925072460141773214187520

noncomputable def p9240 :=
@Enclosure.Real.IsNear.recentre'
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
      true 5))
  false p9238 p9239

noncomputable def p9241 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 101285400 400000)
      (Real.log (Enclosure.sfrac false 41034939012640000 160000000000)))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 1 4)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 1 2) Real.pi)
        (Real.arctan
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@Nat.cast.{0} Real Real.instNatCast 100000)
            (@Nat.cast.{0} Real Real.instNatCast 202570800))))))

noncomputable def p9242 :=
nat_lit 511653257347785099817497383531520000000000000000

noncomputable def p9243 :=
nat_lit 3109380643518799748043154846148220948480000000000000

noncomputable def p9244 :=
@Enclosure.Real.IsNear.of_eq
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
      true 5))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (p9241 (Enclosure.sfrac false 101285400 200000))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 101285400 200000) (Real.log Real.pi)))
    (Enclosure.sfrac true p9242 p9243))
  false

noncomputable def p9245 :=
BSN.riemannSiegelThetaApproximant_two_zero_mk
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
    true 5)
  101285400 100000 41034939012640000 160000000000

noncomputable def p9246 :=
p9245 202570800 400000 200000 p9242
  p9243
  (Enclosure.sfrac_ofScientific_eq 101285400 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9247 :=
@Enclosure.Real.IsNear.addLit_ft_p
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (p9241 (Enclosure.sfrac false 101285400 200000))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 101285400 200000) (Real.log Real.pi)))
  (Enclosure.sfrac true p9242 p9243) 744777142690552315237
  360287970189639680

noncomputable def p9248 :=
nat_lit 2315795446874728971202083479639176714549780123646765382389760000000000000

noncomputable def p9249 :=
@p9247 844674938899010911 p3054 p9242
  p9243 0 1 p9248 p9238
  p9239 844674938899010911 p3054

noncomputable def p9250 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (p9241 (Enclosure.sfrac false 101285400 200000))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 101285400 200000) (Real.log Real.pi))
  23841101231565912358621 9007199254740992000 638317863797 66000000000000000000

noncomputable def p9251 :=
nat_lit 1279517388265699056847998995660800000

noncomputable def p9252 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 101285400 400000)
      (Real.log (Enclosure.sfrac false 41034939012640000 160000000000)))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 1 4)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 1 2) Real.pi)
        (Real.arctan
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@Nat.cast.{0} Real Real.instNatCast 100000)
            (@Nat.cast.{0} Real Real.instNatCast 202570800))))))

noncomputable def p9253 :=
@p9252 (Enclosure.sfrac false 101285400 200000)
  5680518025709325742841 1801439850948198400 638317863797 66000000000000000000
  101285400 200000 0

noncomputable def p9254 :=
nat_lit 953644049262636494344840000

noncomputable def p9255 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 101285400 400000)
    (Real.log (Enclosure.sfrac false 41034939012640000 160000000000)))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 1 4)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 1 2) Real.pi)
      (Real.arctan
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@Nat.cast.{0} Real Real.instNatCast 100000)
          (@Nat.cast.{0} Real Real.instNatCast 202570800)))))
  5681225227162299338841

noncomputable def p9256 :=
nat_lit 12791389431927952516166713935363309568

noncomputable def p9257 :=
@p9255 1801439850948198400 211105951849 22000000000000000000
  884001816216995 2251799813685248 20000033 264000000000000000
  p9256 5680518025709325742841 1801439850948198400 638317863797

noncomputable def p9258 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 101285400 400000)
  (Real.log (Enclosure.sfrac false 41034939012640000 160000000000)) 101285400
  400000 0 1 56091255276301415 4503599627370496

noncomputable def p9259 :=
nat_lit 30836493696422658721731051520

noncomputable def p9260 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast 41034939012640000)
      (@Nat.cast.{0} Real Real.instNatCast 160000000000)))
  false p9259 p2333

noncomputable def p9261 :=
BSN.log_rat_reduce_isNear 41034939012640000 160000000000 17 82069878025280000
  41943040000000000 46128536177 68719476736 24973259072661432
  36028797018963968 26400000000 1000000000000000

noncomputable def p9262 :=
nat_lit
  858264675348755358667464545711331170478994920015140325361450895787696217155439434298537583052531121424154145888662767279146898748278433164371086919611529979607795781185518019577906376951287223652191155972354312435889351956192016278189088761558199663453769125543450049215705592911880096055296000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p9263 :=
nat_lit
  31987532341326332292912043690703467640875004313172444280033483185495700264084384696621225583610085148070986545471823235678777181086809462091653894230130205531026134640312387102297212017762590556455996770325551660884528145226881000573068111413201203859793260873351810523050839496744351930777600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p9264 :=
nat_lit
  618286370713252664343642740387937648608850714042129525257159678967404653459856202301682493074632372948495114655536658117234080282579940568091597482927646220282444781588693340833872028574865789222498873348932549862005150422847760866276945652670075767733140651302283189009359306752000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p9265 :=
BSN.log_dyadic_bound 20063419012640000 62006459012640000 12 11
  p9262 68719476736 26400000000 p9263 p9264
  46128536177 82069878025280000

noncomputable def p9266 :=
p9265 41943040000000000 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p9267 :=
@BSN.binarySplit_of_base11 (BSN.artanhP 20063419012640000) (BSN.artanhQ 62006459012640000)
  0 11 p9263 p9262 p9264
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p9268 :=
p9261 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p9266 (p9267 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

noncomputable def p9269 :=
@p9258 1250561 33000000000000000 5681225227162299338841
  1801439850948198400 211105951849 22000000000000000000
  (Enclosure.Real.IsNear.const false 101285400 400000)
  (BSN.isNear_log_sfrac 41034939012640000 160000000000 56091255276301415
    4503599627370496 1250561 33000000000000000 false
    (@p9260 1000448800000000 p2422 56091255276301415
      4503599627370496 1250561 33000000000000000
      (p9268 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p9270 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 1 4)
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 1 2) Real.pi)
    (Real.arctan
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@Nat.cast.{0} Real Real.instNatCast 100000)
        (@Nat.cast.{0} Real Real.instNatCast 202570800))))
  1 4

noncomputable def p9271 :=
@p9270 0 1 884001816216995 562949953421312 20000033
  66000000000000000 884001816216995 2251799813685248 20000033
  264000000000000000 (Enclosure.Real.IsNear.const false 1 4)

noncomputable def p9272 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 1 2) Real.pi)
  (Real.arctan
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast 100000) (@Nat.cast.{0} Real Real.instNatCast 202570800)))
  884279719003555 562949953421312 1

noncomputable def p9273 :=
nat_lit 7593517780513191928791040

noncomputable def p9274 :=
@p9272 2000000000000000 4240460 8589934592 1
  3300000000 p9273 884001816216995 562949953421312 20000033
  66000000000000000
  (@p803 1 1000000000000000 884279719003555 562949953421312
    1 2000000000000000 (Enclosure.Real.IsNear.const false 1 2)
    BSN.pi_near_15 (Eq.refl true))

noncomputable def p9275 :=
BSN.arctan_dyadic_bound_f 100000 202570800 1 0 8589934592
  3300000000 0 1 1 0 1

noncomputable def p9276 :=
p9275 1 4240460 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)
  (@BSN.binarySplit_of_le (BSN.arctanEvenP 100000) (BSN.arctanEvenQ 202570800) 0
    0 (Eq.refl true))
  (@BSN.binarySplit_of_le (BSN.arctanOddP 100000) (BSN.arctanOddQ 202570800) 0 0
    (Eq.refl true))

noncomputable def p9277 :=
p9271
  (p9274
    (p9276 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p9278 :=
@p9250 39838200869004093 68719476736000 506427 34359738368000
  p9251 744777142690552315237 360287970189639680 844674938899010911
  p3054
  (@p9253 1 p9254 23841101231565912358621
    9007199254740992000 638317863797 66000000000000000000
    (@p9257 66000000000000000000 p9269 p9277
      (Eq.refl true) (Eq.refl true))
    (Enclosure.Real.IsNear.const false 101285400 200000) (Eq.refl true)
    (Eq.refl true))

noncomputable def p9279 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 101285400 200000) (Real.log Real.pi)
  101285400 200000 0 1 78665238759 68719476736

noncomputable def p9280 :=
p9278
  (@p9279 1 34359738368 39838200869004093 68719476736000
    506427 34359738368000
    (Enclosure.Real.IsNear.const false 101285400 200000) d91
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p9281 :=
@p9237 17179869184 105 4294967296 false 17179751622
  17179869184 1 3300000000
  (@p9240 844674938899010911 p3054 35513738794547
    17179869184 105 4294967296
    (@p9244 p9238 p9239 844674938899010911
      p3054
      (p9246 (Eq.refl true) (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (p9249 (p9280 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p9242 p9243)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p9282 :=
nat_lit 9159420208413534756798464

noncomputable def p9283 :=
BSN.cos_reduce0
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 35513738794547)
    (@Nat.cast.{0} Real Real.instNatCast 17179869184))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast p9282)
    (@Nat.cast.{0} Real Real.instNatCast p2333))
  226375608064910080 72057594037927936 false

noncomputable def p9284 :=
BSN.sin_reduce_arg_pos_rat_q0 35513738794547 17179869184 226375608064910080
  72057594037927936 329 p9282 p2333
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p9285 :=
BSN.cos_dyadic_bound_f 130163189857 35184372088832 1 0 17179869184
  6606445313 0 1 1 0 1

noncomputable def p9286 :=
p9285 1 17179751622 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (@BSN.binarySplit_of_le (BSN.cosEvenP 130163189857) (BSN.cosEvenQ 35184372088832) 0
    0 (Eq.refl true))

noncomputable def p9287 :=
p9286
  (@BSN.binarySplit_of_le (BSN.cosOddP 130163189857) (BSN.cosOddQ 35184372088832) 0
    0 (Eq.refl true))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p9288 :=
@BSN.cos_arg_round false 17179751622 17179869184 p9282
  p2333 130163189857 35184372088832 6606445313 6600000000
  p9287 (Eq.refl true)

noncomputable def p9289 :=
p9283 17179751622 17179869184 329 1000000000000000
  6600000000 3300000000 p9284 BSN.pi_near_15 p9288
  (Eq.refl true) (Eq.refl true)

noncomputable def p9290 :=
@p9235 8589934592 1370292841 55364812800000000
  (BSN.main_sum_rs_one
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
      true 5))
  (@p9236 17179869184 350794967296 14173392076800000000
    8589875811 8589934592 1370292841 55364812800000000
    (p9281 (Enclosure.sfrac_false_div 35513738794547 17179869184)
      (p9289 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p9291 :=
@p9233 false 8589875811 8589934592 1370292841
  55364812800000000 137438012976 137438953472 3402 137438953472
  p9290 (Eq.refl true)

noncomputable def p9292 :=
p9232 BSN.abs_quadSignPos (BSN.cos_quad_nat3 607 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 112938028789 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101285400 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true) p9291
  (@p9240 844674938899010911 p3054 284109910356378
    137438953472 3356 137438953472
    (@p9244 p9238 p9239 844674938899010911
      p3054
      (p9246 (Eq.refl true) (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (p9249 (p9280 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p9242 p9243)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p9293 :=
nat_lit 26420567195209746081558378835856707210000

noncomputable def p9294 :=
BSN.sin_dyadic_bound_f 12749276330 137438953472 2 1 137438953472
  68719476736 p9293 p3178 p9293 p9293
  p3179

noncomputable def p9295 :=
@BSN.binarySplit_of_base (BSN.sinEvenP 12749276330) (BSN.sinEvenQ 137438953472) 0
  1 p9293 p3178 p9293 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9296 :=
p9294 p9293 12730999586 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p9295 (Eq.refl true))

noncomputable def p9297 :=
@BSN.binarySplit_of_base (BSN.sinOddP 12749276330) (BSN.sinOddQ 137438953472) 0
  1 p9293 p3179 p9293 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9298 :=
nat_lit
  2040092314537688710684027926602220503608473386989005122364348250184490962697296799033680082369586170299931613076647031786802617022178225889281

noncomputable def p9299 :=
nat_lit
  29420047576303874816453970409897897888468754818939145406892936076420664433304207810614292056268837407377258861057719598222528782868481

noncomputable def p9300 :=
nat_lit
  10198657862369318550065569665958326131898494634168913223767717016499989694261619287197758312442757675746081576400713886391223376463201304125441

noncomputable def p9301 :=
BSN.sin_dyadic_bound_f 132552202241 137438953472 4 3 137438953472
  68719476736 p9298 p2504 p9299 p9300
  p2507

noncomputable def p9302 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 132552202241) (BSN.sinEvenQ 137438953472) 0
  3 p9298 p2504 p9299 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9303 :=
p9301 p9299 112938028789 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p9302 (Eq.refl true))

noncomputable def p9304 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 132552202241) (BSN.sinOddQ 137438953472) 0
  3 p9300 p2507 p9299 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9305 :=
p9292 d93 d95 d97 d99 d103
  (p9296 (p9297 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p9303 (p9304 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p9306 :=
p9227 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 278 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 128401694362 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101285400 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p9305 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p9240 844674938899010911 p3054 284109910356378
    137438953472 3356 137438953472
    (@p9244 p9238 p9239 844674938899010911
      p3054
      (p9246 (Eq.refl true) (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (p9249 (p9280 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p9242 p9243)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p9307 :=
nat_lit 233786785513128971369357611624895811290454424849811976595876493853231000230362582381342881

noncomputable def p9308 :=
nat_lit 152104503953147588092717624959363295274133895608139720385530673980913524014001008801

noncomputable def p9309 :=
nat_lit 701360052330379007812896649439437515144772726281644713508188710498345038864039719142011041

noncomputable def p9310 :=
BSN.cos_dyadic_bound_f 24990086493 137438953472 3 2 137438953472
  68719476736 p9307 p2466 p9308 p9309
  p2469

noncomputable def p9311 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP 24990086493) (BSN.cosEvenQ 137438953472) 0
  2 p9307 p2466 p9308 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9312 :=
p9310 p9308 135173272087 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p9311 (Eq.refl true))

noncomputable def p9313 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP 24990086493) (BSN.cosOddQ 137438953472) 0
  2 p9309 p2469 p9308 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9314 :=
nat_lit 3782180025601805367601347504707691696345381884325920638369126552102964584218529330261774401

noncomputable def p9315 :=
nat_lit 39808697779719482133932413977083025433282286962467041798811372294182506471990778515521

noncomputable def p9316 :=
nat_lit 11346460459409856663839774649295120922985279088403836981023782033564305387642644009228292161

noncomputable def p9317 :=
BSN.cos_dyadic_bound_f 50118405591 137438953472 3 2 137438953472
  68719476736 p9314 p2466 p9315 p9316
  p2469

noncomputable def p9318 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP 50118405591) (BSN.cosEvenQ 137438953472) 0
  2 p9314 p2466 p9315 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9319 :=
p9317 p9315 128401694362 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p9318 (Eq.refl true))

noncomputable def p9320 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP 50118405591) (BSN.cosOddQ 137438953472) 0
  2 p9316 p2469 p9315 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9321 :=
p9306 d105 d107 d109 d111 d103
  (p9312 (p9313 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p9319 (p9320 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p9322 :=
p9223 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 61 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 57320720128 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101285400 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p9321 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p9240 844674938899010911 p3054 284109910356378
    137438953472 3356 137438953472
    (@p9244 p9238 p9239 844674938899010911
      p3054
      (p9246 (Eq.refl true) (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (p9249 (p9280 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p9242 p9243)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p9323 :=
nat_lit
  1117669384180631047539563361561438860730373495024775138276341473579707689556886065289126791013187285341707649433698484533781214658272249122816

noncomputable def p9324 :=
nat_lit
  84912510513591839125303854041274053544592745705620968511243337856651407059411581977073983331832285143535277935633548490575276880039936

noncomputable def p9325 :=
nat_lit
  6777215125454811709128333365854864819889511533881444269947488379981614654622189878253050055890115188514880682229749840607539668466427036569600

noncomputable def p9326 :=
BSN.cos_dyadic_bound_f 144793024558 137438953472 4 3 137438953472
  68719476736 p9323 p2457 p9324 p9325
  p2460

noncomputable def p9327 :=
@BSN.binarySplit_of_base3 (BSN.cosEvenP 144793024558) (BSN.cosEvenQ 137438953472) 0
  3 p9323 p2457 p9324 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9328 :=
p9326 p9324 67967019155 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p9327 (Eq.refl true))

noncomputable def p9329 :=
@BSN.binarySplit_of_base3 (BSN.cosOddP 144793024558) (BSN.cosOddQ 137438953472) 0
  3 p9325 p2460 p9324 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9330 :=
nat_lit 13188453953322100644734965307083345414792725149675995118075666991675636405101271591037340545

noncomputable def p9331 :=
nat_lit 149394856468119441743552990679434816557251410417634803773182846198333341282025069513601

noncomputable def p9332 :=
nat_lit 34540947047980743780923991004185757001420806508772644376706352205970917092712683269270965121

noncomputable def p9333 :=
BSN.sin_dyadic_bound_f 59127832049 137438953472 3 2 137438953472
  68719476736 p9330 p2477 p9331 p9332
  p2480

noncomputable def p9334 :=
@BSN.binarySplit_of_base2 (BSN.sinEvenP 59127832049) (BSN.sinEvenQ 137438953472) 0
  2 p9330 p2477 p9331 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9335 :=
p9333 p9331 57320720128 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p9334 (Eq.refl true))

noncomputable def p9336 :=
@BSN.binarySplit_of_base2 (BSN.sinOddP 59127832049) (BSN.sinOddQ 137438953472) 0
  2 p9332 p2480 p9331 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9337 :=
p9322 d113 d115 d117 d119 d103
  (p9328 (p9329 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p9335 (p9336 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p9338 :=
p9218 BSN.abs_quadSignPos (BSN.cos_quad_nat0 100 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 47694161794 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101285400 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p9337 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p9240 844674938899010911 p3054 284109910356378
    137438953472 3356 137438953472
    (@p9244 p9238 p9239 844674938899010911
      p3054
      (p9246 (Eq.refl true) (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (p9249 (p9280 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p9242 p9243)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p9339 :=
nat_lit
  2593158731786700093038479719828728753718990959184954267947442279121599849398709998787187742818929838632866362390384175705643470346278464000000

noncomputable def p9340 :=
nat_lit
  1057452815862903655761816042106502597785114896447481529375695860871607803741207094505649319602031286322970034376760537200081000000000000

noncomputable def p9341 :=
nat_lit
  15714029663645357641931506130505856118047401913908424334084667730088540018239302396604590293891700887386015837597970606837229492686417881600000

noncomputable def p9342 :=
BSN.cos_dyadic_bound_f 178657704590 137438953472 4 3 137438953472
  68719476736 p9339 p2457 p9340 p9341
  p2460

noncomputable def p9343 :=
@BSN.binarySplit_of_base3 (BSN.cosEvenP 178657704590) (BSN.cosEvenQ 137438953472) 0
  3 p9339 p2457 p9340 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9344 :=
p9342 p9340 36777222449 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p9343 (Eq.refl true))

noncomputable def p9345 :=
@BSN.binarySplit_of_base3 (BSN.cosOddP 178657704590) (BSN.cosOddQ 137438953472) 0
  3 p9341 p2460 p9340 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9346 :=
nat_lit
  1987561500765449311760480885264675594926030578326676316560927191374595125312247077146938693272947404649146969579301151631323071626697293568721

noncomputable def p9347 :=
nat_lit
  476706772775314555139246960863688457127788220650257643614829301835516493146311651197030084288320993551903394897777739745861566533868241

noncomputable def p9348 :=
nat_lit
  12047408669120975503031195101582252509282396953552516132677913684580873004291249277738217365129054150297478847513179003773140433750282008664785

noncomputable def p9349 :=
BSN.cos_dyadic_bound_f 167181266203 137438953472 4 3 137438953472
  68719476736 p9346 p2457 p9347 p9348
  p2460

noncomputable def p9350 :=
@BSN.binarySplit_of_base3 (BSN.cosEvenP 167181266203) (BSN.cosEvenQ 137438953472) 0
  3 p9346 p2457 p9347 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9351 :=
p9349 p9347 47694161794 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p9350 (Eq.refl true))

noncomputable def p9352 :=
@BSN.binarySplit_of_base3 (BSN.cosOddP 167181266203) (BSN.cosOddQ 137438953472) 0
  3 p9348 p2460 p9347 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9353 :=
p9338 d121 d123 d125 d127 d103
  (p9344 (p9345 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p9351 (p9352 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p9354 :=
p9214 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 230 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 132713108241 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101285400 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p9353 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p9240 844674938899010911 p3054 284109910356378
    137438953472 3356 137438953472
    (@p9244 p9238 p9239 844674938899010911
      p3054
      (p9246 (Eq.refl true) (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (p9249 (p9280 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p9242 p9243)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p9355 :=
nat_lit
  1413099962818949412362378396547689759724503680652081377331937101877437548554799188512039530367656751831189411758260724908008048378696345583616

noncomputable def p9356 :=
nat_lit
  171513432948701901526845400659969913404854051648547668618094161195583257261856499892050878954483725119686903715171459465037871616884736

noncomputable def p9357 :=
nat_lit
  8567513243931443899879457001995507557398709617454415188099111660623752393873563482354102065988044410267769259515627616809418203891168916275200

noncomputable def p9358 :=
BSN.cos_dyadic_bound_f 153529385492 137438953472 4 3 137438953472
  68719476736 p9355 p2457 p9356 p9357
  p2460

noncomputable def p9359 :=
@BSN.binarySplit_of_base3 (BSN.cosEvenP 153529385492) (BSN.cosEvenQ 137438953472) 0
  3 p9355 p2457 p9356 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9360 :=
p9358 p9356 60241541052 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p9359 (Eq.refl true))

noncomputable def p9361 :=
@BSN.binarySplit_of_base3 (BSN.cosOddP 153529385492) (BSN.cosOddQ 137438953472) 0
  3 p9357 p2460 p9356 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9362 :=
nat_lit 1023288190850612060547739868843409582280474308683008242231554343766189327565660825069879296

noncomputable def p9363 :=
nat_lit 2914044442400100482356563159533013228868271530541169375283173844854387546696796143616

noncomputable def p9364 :=
nat_lit 3069858744462951381442254893403909680814965189505963644355912464950878273921889081617350656

noncomputable def p9365 :=
BSN.cos_dyadic_bound_f 36146147908 137438953472 3 2 137438953472
  68719476736 p9362 p2466 p9363 p9364
  p2469

noncomputable def p9366 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP 36146147908) (BSN.cosEvenQ 137438953472) 0
  2 p9362 p2466 p9363 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9367 :=
p9365 p9363 132713108241 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p9366 (Eq.refl true))

noncomputable def p9368 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP 36146147908) (BSN.cosOddQ 137438953472) 0
  2 p9364 p2469 p9363 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9369 :=
p9354 d129 d131 d133 d135 d103
  (p9360 (p9361 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p9367 (p9368 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p9370 :=
p9209
  (p9369 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p9240 844674938899010911 p3054 284109910356378
    137438953472 3356 137438953472
    (@p9244 p9238 p9239 844674938899010911
      p3054
      (p9246 (Eq.refl true) (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (p9249 (p9280 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p9242 p9243)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p9371 :=
nat_lit 7192564712625576894485215571206810402907378641777042588773572252178108707293518689592413761

noncomputable def p9372 :=
nat_lit 143963663729610428917652963577493005584503200091679666369733771587428954162917370236481

noncomputable def p9373 :=
nat_lit 21577406210549271462597811407693276222710966918930944406987977288991151263972230234036768321

noncomputable def p9374 :=
BSN.cos_dyadic_bound_f 58854762473 137438953472 3 2 137438953472
  68719476736 p9371 p2466 p9372 p9373
  p2469

noncomputable def p9375 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP 58854762473) (BSN.cosEvenQ 137438953472) 0
  2 p9371 p2466 p9372 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9376 :=
p9374 p9372 125028815743 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p9375 (Eq.refl true))

noncomputable def p9377 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP 58854762473) (BSN.cosOddQ 137438953472) 0
  2 p9373 p2469 p9372 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9378 :=
p9370 d137 d139 d103
  (p9376 (p9377 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true) (Eq.refl true)

noncomputable def p9379 :=
@p9198 p9182 p9184 p9185
  (p9202
    (@p9205 217591 68719476736
      (p9378 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (p9378 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true) (Eq.refl true)))

noncomputable def p9380 :=
@Enclosure.Real.IsNear.mulLit_ff p9189
  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
        (Enclosure.sfrac false 12 1)))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Zeta.RiemannSiegel.correctionLinear
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
          (Enclosure.sfrac false 12 1)))
      (@Inv.inv.{0} Real Real.instInv p9190)))

noncomputable def p9381 :=
nat_lit
  407212985619972222363852618686959441519546953047070957680670398834891195365269075138539650325521523835127040837253755499220064263954080557016314400606330818280991

noncomputable def p9382 :=
nat_lit
  899782758908639276562107701537196371773939423660383326620151114522367516134297574063808137220778171429984182126704179024641653211098859937801703036173032771026944

noncomputable def p9383 :=
nat_lit
  13580016557287334384800643303704751291705407975072663286352112907902656456018414273702620530053366932559511218627360611440910618020470944643993359465143431751587405862403679661193959300949648091449901440818240823507

noncomputable def p9384 :=
@p9380 4821454889 17179869184 1 17179869184
  p9381 p9382 p9383 p4975
  p9195 p9182 p9196

noncomputable def p9385 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HPow.hPow.{0, 0, 0} Real Nat Real
    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
    (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)))
    12)
  (p9188
    (@Neg.neg.{0} Real Real.instNeg
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
        (@OfNat.ofNat.{0} Real 4
          (@instOfNatAtLeastTwo.{0} Real 4 Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))))))

noncomputable def p9386 :=
@p9385 1 1 0 1 4821454889 17179869184
  1 17179869184 4821454889 17179869184 1

noncomputable def p9387 :=
@Enclosure.Real.IsNear.of_eq
  (p9188
    (@Neg.neg.{0} Real Real.instNeg
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
        (@OfNat.ofNat.{0} Real 4
          (@instOfNatAtLeastTwo.{0} Real 4 Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))))))

noncomputable def p9388 :=
BSN.rpow_neg_quarter_mk
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p9389 :=
p9388
  (BSN.t_div_two_pi_nonneg
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
      true 5)
    101285400 100000
    (Enclosure.sfrac_ofScientific_eq 101285400 5 100000 (Eq.refl true)))

noncomputable def p9390 :=
@Enclosure.Real.IsNear.recentre' (@Inv.inv.{0} Real Real.instInv (Real.sqrt p9190)) false
  4821454889 17179869184 1 17179869184 4821454889
  17179869184

noncomputable def p9391 :=
@Enclosure.Real.IsNear.recentre' (Real.sqrt p9190) false 61215527670
  17179869184 6 17179869184 30607763835 8589934592 3
  8589934592

noncomputable def p9392 :=
@Enclosure.Real.IsNear.sqrt_image
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p9393 :=
@Enclosure.Real.IsNear.of_eq
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p9394 :=
@p9393
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 101285400 100000)
    (@Inv.inv.{0} Real Real.instInv
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)))
  false 1384703647608981

noncomputable def p9395 :=
@p9394 8589934592000 506427 8589934592000
  (BSN.t_div_two_pi_mk
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
      true 5)
    101285400 100000
    (Enclosure.sfrac_ofScientific_eq 101285400 5 100000 (Eq.refl true)))

noncomputable def p9396 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 101285400 100000)
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi))
  101285400 100000 0

noncomputable def p9397 :=
@p9396 1 2734261103 17179869184 1 17179869184
  1384703647608981 8589934592000 506427 8589934592000
  (Enclosure.Real.IsNear.const false 101285400 100000) d142

noncomputable def p9398 :=
@p9392 1384703647608981 8589934592000 506427 8589934592000
  109061972098 109061972138 8589934592
  (p9395 (p9397 (Eq.refl true))) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9399 :=
@Enclosure.Real.IsNear.recentre' p9190 false 218123944236 17179869184
  40 17179869184 54530986059 4294967296 5 2147483648
  (p9398 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p9400 :=
@Enclosure.Real.IsNear.sqrt_image p9190 54530986059 4294967296 5
  2147483648 30607763832 30607763838 8589934592
  (p9399 (Eq.refl true)) (Eq.refl true) (Eq.refl true)

noncomputable def p9401 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt p9190) 30607763835 8589934592
  3 8589934592 2410727444 2410727445 8589934592
  (p9391
    (p9400 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p9402 :=
@p9387 (@Inv.inv.{0} Real Real.instInv (Real.sqrt p9190)) false
  4821454889 17179869184 1 17179869184 p9389
  (@p9390 1 17179869184
    (p9401 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p9403 :=
@Enclosure.Real.IsNear.addLit_ft_p
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
      (Enclosure.sfrac false 12 1)))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Zeta.RiemannSiegel.correctionLinear
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
        (Enclosure.sfrac false 12 1)))
    (@Inv.inv.{0} Real Real.instInv p9190))
  66895718247741823167

noncomputable def p9404 :=
nat_lit 1902320482601297510400000000

noncomputable def p9405 :=
nat_lit
  661255517205716161376342314818411054468029669396884515149020442729892719619396804797862737848137979401123627014113002244857303192898924506119823284202805510625

noncomputable def p9406 :=
nat_lit
  73968231768997574835577915287789164753510508782029004365810559990964578882220182443840293309805321751735666457899007645593397269443138457453829155047810583862468620801226553731319766983216030483300480272746941169

noncomputable def p9407 :=
nat_lit
  34870544834271577651716587098237417512867145848661684127600797306728414633224631076188203166925495872307606581534205906534007119690292194495692800000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p9408 :=
nat_lit
  60094029833782363642542979163700648686538053916983340117830126627704500457286591573741170648457463385664853544373092649948802174402516211179341637141715893197731233518065780049051648

noncomputable def p9409 :=
@p9403 147573952589676412928 242911889530230295057 p9404
  p9405 p9382 p9406 p9407
  p9408 p9381 p9382 p9383

noncomputable def p9410 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (@Inv.inv.{0} Real Real.instInv
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
          (Enclosure.sfrac false 12 1)))))

noncomputable def p9411 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
        (Enclosure.sfrac false 12 1))
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
        (Enclosure.sfrac false 12 1)))
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
      (Enclosure.sfrac false 12 1)))

noncomputable def p9412 :=
@Enclosure.Real.IsNear.of_eq
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
      (Enclosure.sfrac false 12 1)))
  (p9410
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p9411 (Enclosure.sfrac false 1 16)))))

noncomputable def p9413 :=
BSN.cos_two_pi_p_ne_zero_mk
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
    true 5)
  101285400 100000 12
  (Enclosure.sfrac_ofScientific_eq 101285400 5 100000 (Eq.refl true))

noncomputable def p9414 :=
@Enclosure.Real.IsNear.mulLit_tt
  (@Inv.inv.{0} Real Real.instInv
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
          (Enclosure.sfrac false 12 1)))))

noncomputable def p9415 :=
@p9414
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p9411 (Enclosure.sfrac false 1 16))))
  52068594513

noncomputable def p9416 :=
@p9415 17179869184 2363 17179869184 1284761359
  8589934592 3913632557 110729625600000000 66895718247741823167
  147573952589676412928 242911889530230295057 p9404

noncomputable def p9417 :=
@Enclosure.Real.IsNear.of_eq
  (@Inv.inv.{0} Real Real.instInv
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
          (Enclosure.sfrac false 12 1)))))

noncomputable def p9418 :=
@Inv.inv.{0} Real Real.instInv
  (@Neg.neg.{0} Real Real.instNeg
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
          (Enclosure.sfrac false 12 1)))))

noncomputable def p9419 :=
@p9417 (@Neg.neg.{0} Real Real.instNeg p9418) true 52068594513
  17179869184 2363 17179869184
  (BSN.inv_eq_neg_inv_neg
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
          (Enclosure.sfrac false 12 1)))))

noncomputable def p9420 :=
@Enclosure.Real.IsNear.inv_image
  (@Neg.neg.{0} Real Real.instNeg
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
          (Enclosure.sfrac false 12 1)))))

noncomputable def p9421 :=
@Enclosure.Real.IsNear.neg
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
        (Enclosure.sfrac false 12 1))))
  true

noncomputable def p9422 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
        (Enclosure.sfrac false 12 1))))
  true

noncomputable def p9423 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
      (Enclosure.sfrac false 12 1)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 75181541933)
    (@Nat.cast.{0} Real Real.instNatCast 17179869184))
  false

noncomputable def p9424 :=
nat_lit 2645215345603233883592385

noncomputable def p9425 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
      (Enclosure.sfrac false 12 1)))
  false p9424

noncomputable def p9426 :=
nat_lit 134930389893093084798151907

noncomputable def p9427 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
    (Enclosure.sfrac false 12 1))
  884279719003555 140737488355328 1

noncomputable def p9428 :=
@Enclosure.Real.IsNear.subLit_ff_p p9190 (Enclosure.sfrac false 12 1)
  54530986059 4294967296 5 2147483648 12 1 0

noncomputable def p9429 :=
@p9427 500000000000000 2991378507 4294967296 5
  2147483648 p9424 604462909807314587353088 p9426
  p7830 d141
  (@p9428 1 2991378507 2991378507 4294967296 5
    2147483648 (p9399 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p9430 :=
@p9423 75181541933 17179869184 63 4294967296 true
  5668443866 17179869184 1 3300000000
  (@p9425 604462909807314587353088 p9426 p7830
    75181541933 17179869184 63 4294967296
    (p9429 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div 75181541933 17179869184)

noncomputable def p9431 :=
nat_lit 3056595389499918715386331136

noncomputable def p9432 :=
BSN.cos_reduce2
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 75181541933)
    (@Nat.cast.{0} Real Real.instNatCast 17179869184))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast p9431)
    (@Nat.cast.{0} Real Real.instNatCast p2333))
  226375608064910080 72057594037927936 false

noncomputable def p9433 :=
BSN.sin_reduce_arg_pos_rat_q2 75181541933 17179869184 226375608064910080
  72057594037927936 0 p9431 p2333 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p9434 :=
nat_lit
  167092505106758960987561762881484924856008985021936577312907361401569364796911913709889733615154495221726390002368413225436763576285586642952006534784633424442584337165201

noncomputable def p9435 :=
nat_lit
  45112597930226530960947146978173400373448067986047370792573593150313221618640468498309568120609868832775862583197706029799228071496490777790963760174882689591749521

noncomputable def p9436 :=
nat_lit
  1012761177551188823277244513624424595142402676150525342066531870963359497317022863192808164086688460218188190540521810379987353747684729983561341764777673842903698009435025

noncomputable def p9437 :=
BSN.cos_dyadic_bound_f 43436833003339 35184372088832 4 3 17179869184
  6606445313 p9434 p2613 p9435 p9436
  p2616

noncomputable def p9438 :=
@BSN.binarySplit_of_base3 (BSN.cosEvenP 43436833003339) (BSN.cosEvenQ 35184372088832) 0
  3 p9434 p2613 p9435 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9439 :=
p9437 p9435 5668443866 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p9438 (Eq.refl true))

noncomputable def p9440 :=
@BSN.binarySplit_of_base3 (BSN.cosOddP 43436833003339) (BSN.cosOddQ 35184372088832) 0
  3 p9436 p2616 p9435 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9441 :=
@BSN.cos_arg_round false 5668443866 17179869184 p9431 p2333
  43436833003339 35184372088832 6606445313 6600000000
  (p9439 (p9440 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p9442 :=
p9432 5668443866 17179869184 0 1000000000000000
  6600000000 3300000000 p9433 BSN.pi_near_15 p9441
  (Eq.refl true) (Eq.refl true)

noncomputable def p9443 :=
@p9421 2834221933 8589934592 828886591 55364812800000000
  (@p9422 5668443866 17179869184 212194967296
    14173392076800000000 2834221933 8589934592 828886591
    55364812800000000
    (p9430 (p9442 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p9444 :=
@p9420 2834221933 8589934592 828886591 55364812800000000
  26034296075 26034298438 8589934592 p9443 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9445 :=
@Enclosure.Real.IsNear.recentre' p9418 false 52068594513 17179869184
  2363 17179869184 52068594513 17179869184 2363 17179869184
  (p9444 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p9446 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p9411 (Enclosure.sfrac false 1 16))))
  true

noncomputable def p9447 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p9411 (Enclosure.sfrac false 1 16)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Neg.neg.{0} Real Real.instNeg (@Nat.cast.{0} Real Real.instNatCast 1847829743))
    (@Nat.cast.{0} Real Real.instNatCast 1073741824))
  true

noncomputable def p9448 :=
nat_lit 4467778173146034618158121216771445

noncomputable def p9449 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p9411 (Enclosure.sfrac false 1 16)))
  true p9448

noncomputable def p9450 :=
nat_lit 2596148429267413814265248164610048

noncomputable def p9451 :=
nat_lit 43336788730141651447933522665531247

noncomputable def p9452 :=
nat_lit 1237940039285380274899124224000000000000000

noncomputable def p9453 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (p9411 (Enclosure.sfrac false 1 16)) 884279719003555
  140737488355328 1

noncomputable def p9454 :=
@Enclosure.Real.IsNear.subLit_tf
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
        (Enclosure.sfrac false 12 1))
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
        (Enclosure.sfrac false 12 1)))
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
      (Enclosure.sfrac false 12 1)))

noncomputable def p9455 :=
@p9454 (Enclosure.sfrac false 1 16) 3899527485380758023
  18446744073709551616 1605894425 288230376151711744 1 16 0

noncomputable def p9456 :=
@Enclosure.Real.IsNear.subLit_ff_n
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
      (Enclosure.sfrac false 12 1))
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
      (Enclosure.sfrac false 12 1)))
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
    (Enclosure.sfrac false 12 1))
  8948345372141549049

noncomputable def p9457 :=
nat_lit 16748343019563473816474615808

noncomputable def p9458 :=
@p9456 18446744073709551616 934805785 288230376151711744
  2991378507 4294967296 5 2147483648 p9457
  3899527485380758023 18446744073709551616 1605894425

noncomputable def p9459 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
    (Enclosure.sfrac false 12 1))
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
    (Enclosure.sfrac false 12 1))
  2991378507 4294967296 5

noncomputable def p9460 :=
@p9459 2147483648 2991378507 4294967296 5 2147483648
  8948345372141549049 18446744073709551616 934805785 288230376151711744
  (@p9428 1 2991378507 2991378507 4294967296 5
    2147483648 (p9399 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p9461 :=
p9460
  (@p9428 1 2991378507 2991378507 4294967296 5
    2147483648 (p9399 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p9462 :=
@p9458 288230376151711744 (p9461 (Eq.refl true))
  (@p9428 1 2991378507 2991378507 4294967296 5
    2147483648 (p9399 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p9463 :=
@p9453 500000000000000 5052448989987604999 18446744073709551616
  1605894425 288230376151711744 p9448 p9450
  p9451 p9452 d141
  (@p9455 1 80839183839801679984 5052448989987604999
    18446744073709551616 1605894425 288230376151711744
    (p9462 (Eq.refl true) (Eq.refl true))
    (Enclosure.Real.IsNear.const false 1 16) (Eq.refl true)
    (Eq.refl true))

noncomputable def p9464 :=
@p9447 1847829743 1073741824 301 8589934592 true
  1284761359 8589934592 1 3300000000
  (@p9449 p9450 p9451 p9452 1847829743
    1073741824 301 8589934592 (p9463 (Eq.refl true))
    (Eq.refl true))
  (Enclosure.sfrac_true_div 1847829743 1073741824)

noncomputable def p9465 :=
nat_lit
  23994833834668289677576582800198741795996430141587436897254888386565576994452083357137161474855524383436787964465651440220120498644008405676732124672255207681

noncomputable def p9466 :=
nat_lit
  65315689001430101463437438788805272313419085489526239767007691747054552085219169171183189876641515636152014546297038989853108186772682866843307077206540288000

noncomputable def p9467 :=
nat_lit
  18475289527820108882246951232011332335604784185688695697392593374534019230723168808003259543124487680268463724109988685013471520414176346005183801601

noncomputable def p9468 :=
nat_lit
  243899093626358478605204439381497663716664469515825448925434317987479974035048505539180460732979593207131831120345691670883879227635907212215104301594870688001

noncomputable def p9469 :=
nat_lit
  9993300417218805523905928134687206663953120079897514684352176837299346469038532883191028051126151892331258225583446965447525552576220478627025982812600664064000

noncomputable def p9470 :=
BSN.cos_dyadic_bound_t 1847829743 1073741824 5 4 8589934592
  3300000000 p9465 p9466 p9467 p9468
  p9469

noncomputable def p9471 :=
@BSN.binarySplit_of_base4 (BSN.cosEvenP 1847829743) (BSN.cosEvenQ 1073741824) 0
  4 p9465 p9466 p9467 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9472 :=
p9470 p9467 1284761359 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p9471 (Eq.refl true))

noncomputable def p9473 :=
@BSN.binarySplit_of_base4 (BSN.cosOddP 1847829743) (BSN.cosOddQ 1073741824) 0 4
  p9468 p9469 p9467 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9474 :=
p9464
  (BSN.cos_neg_of_bound 1847829743 1073741824 true 1284761359 8589934592
    1 3300000000
    (p9472 (p9473 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p9475 :=
p9416
  (p9419
    (@Enclosure.Real.IsNear.neg p9418 false 52068594513 17179869184
      2363 17179869184 (p9445 (Eq.refl true))))
  (@p9446 1284761359 8589934592 1001889934592
    28346784153600000000 1284761359 8589934592 3913632557
    110729625600000000 (p9474 (Eq.refl true)) (Eq.refl true))

noncomputable def p9476 :=
@p9409 p4975
  (@p9412 false 66895718247741823167 147573952589676412928
    242911889530230295057 p9404
    (BSN.correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
        (Enclosure.sfrac false 12 1))
      (p9413 (Eq.refl true) (Eq.refl true)
        (p9193 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p9475 (Eq.refl true)))

noncomputable def p9477 :=
nat_lit
  488689429953629034057468691550464012168992981555939143592920942582436605283879468041670503273331243374409441868163586880322023725157596596526805325875

noncomputable def p9478 :=
nat_lit
  52374249726338269920211035149241586435466272736689036631732661889538140742474792878132321477214466514414186946040961136147476104734166288853256441430016

noncomputable def p9479 :=
@Enclosure.Real.IsNear.mulLit_tf
  (Zeta.RiemannSiegel.correctionLinear
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
      (Enclosure.sfrac false 12 1)))
  (@Inv.inv.{0} Real Real.instInv p9190) p9477 p9478

noncomputable def p9480 :=
nat_lit
  655811319401362263583463233088902164775331454740559607241445953835059120924119698010832004901949131930381945991270631102876841105798310576572173671919952796261590113490198831526378475097934700576762509513

noncomputable def p9481 :=
nat_lit
  24356794194973710215452537242023333101207725132346398286242594923867202340549298848156959167862424537754342831811545817088806386820710400000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p9482 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
      (Enclosure.sfrac false 12 1)))
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 96 1)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi)))

noncomputable def p9483 :=
@Enclosure.Real.IsNear.of_eq
  (Zeta.RiemannSiegel.correctionLinear
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
      (Enclosure.sfrac false 12 1)))
  (@Neg.neg.{0} Real Real.instNeg p9482) true p9477

noncomputable def p9484 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
      (Enclosure.sfrac false 12 1)))
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 96 1)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi)))

noncomputable def p9485 :=
nat_lit
  105279570890927330942397434952104942819573030780763828293914760475008605053371540190305590618835240239278440453105107926227090390111417094725

noncomputable def p9486 :=
nat_lit
  11908525658859223294760121268437066290850060053501019099651935423375594096449911575776314174894302258147533153997065059263030913083222523904

noncomputable def p9487 :=
nat_lit
  10171620329546926949939758521044697718517707230276007404559773561162660197803714611030451489282122394392365803126924894024195145715362706651095908024004542479308827543616662387175125245950129434571

noncomputable def p9488 :=
@p9484 p9485 p9486 p9487 p3309
  4641825815 4398046511104 1 4398046511104 p9477
  p9478 p9480

noncomputable def p9489 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p9490 :=
p9489
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p9491 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p9490
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p9492 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p9491
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p9411 (Enclosure.sfrac false 1 16)))))

noncomputable def p9493 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (Enclosure.sfrac false 3 1)
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p9494 :=
p9492
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p9493
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 4 1) Real.pi))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p9411 (Enclosure.sfrac false 1 16)))))

noncomputable def p9495 :=
@Neg.neg.{0} Real Real.instNeg
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
          (Enclosure.sfrac false 12 1)))))

noncomputable def p9496 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9494
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 3 1) p9495)
    (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
        (Enclosure.sfrac false 12 1))))

noncomputable def p9497 :=
@Neg.neg.{0} Real Real.instNeg
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 4 1)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
          (Enclosure.sfrac false 12 1)))))

noncomputable def p9498 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9496
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 3 1) p9497)
    (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
        (Enclosure.sfrac false 12 1))))

noncomputable def p9499 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 8 1)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi) Real.pi))
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
        (Enclosure.sfrac false 12 1))))

noncomputable def p9500 :=
@Enclosure.Real.IsNear.of_eq
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
      (Enclosure.sfrac false 12 1)))
  (p9410
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9498
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p9499
        (Zeta.RiemannSiegel.correction
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
            (Enclosure.sfrac false 12 1))))))

noncomputable def p9501 :=
@p9414
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9498
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p9499
      (Zeta.RiemannSiegel.correction
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
          (Enclosure.sfrac false 12 1)))))
  6664779905267

noncomputable def p9502 :=
nat_lit
  15796406241071465731475097166288358006351004803821516445304792939612043398527670450191513504846054797586679469222392049560819175

noncomputable def p9503 :=
nat_lit
  5415370496329716522614090203404460358274291162843391748379842930887932241807862544999950011922147613471467208908991351228465152

noncomputable def p9504 :=
nat_lit
  1526078634070658622973488148262592895145176776877081863900263620102176833604317226832019982420610372757403120261750483806640236702681208082541916499441707226979573397012040474631960891

noncomputable def p9505 :=
nat_lit
  181327211478237439808067755131836416461093543234629141236267006266305264275582132804746964834860890954969749913600000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p9506 :=
@p9501 2199023255552 607 1099511627776 p9502
  p9503 p9504 p9505 p9485
  p9486 p9487 p3309

noncomputable def p9507 :=
@p9417 (@Neg.neg.{0} Real Real.instNeg p9418) true 6664779905267
  2199023255552 607 1099511627776
  (BSN.inv_eq_neg_inv_neg
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
          (Enclosure.sfrac false 12 1)))))

noncomputable def p9508 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
      (Enclosure.sfrac false 12 1)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 19246474690605)
    (@Nat.cast.{0} Real Real.instNatCast 4398046511104))
  false

noncomputable def p9509 :=
nat_lit 2708700507650275282038486165

noncomputable def p9510 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
      (Enclosure.sfrac false 12 1)))
  false p9509

noncomputable def p9511 :=
nat_lit 1106455404214357381458918623

noncomputable def p9512 :=
@Enclosure.Real.IsNear.subLit_ff_p p9190 (Enclosure.sfrac false 12 1)
  55839729717351 4398046511104 41 4398046511104 12 1
  0

noncomputable def p9513 :=
@p9393
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 101285400 100000)
    (@Inv.inv.{0} Real Real.instInv
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)))
  false 354484133698261557

noncomputable def p9514 :=
@p9513 2199023255552000 506427 2199023255552000
  (BSN.t_div_two_pi_mk
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
      true 5)
    101285400 100000
    (Enclosure.sfrac_ofScientific_eq 101285400 5 100000 (Eq.refl true)))

noncomputable def p9515 :=
@p9396 1 699970842191 4398046511104 1 4398046511104
  354484133698261557 2199023255552000 506427 2199023255552000
  (Enclosure.Real.IsNear.const false 101285400 100000) d145

noncomputable def p9516 :=
@p9392 354484133698261557 2199023255552000 506427
  2199023255552000 27919864858655 27919864858696 2199023255552
  (p9514 (p9515 (Eq.refl true))) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9517 :=
@Enclosure.Real.IsNear.recentre' p9190 false 55839729717351 4398046511104
  41 4398046511104 55839729717351 4398046511104 41
  4398046511104
  (p9516 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p9518 :=
@p9427 500000000000000 3063171584103 4398046511104 41
  4398046511104 p9509 p504 p9511 p2694
  d144
  (@p9512 1 3063171584103 3063171584103 4398046511104
    41 4398046511104 (p9517 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p9519 :=
@p9508 19246474690605 4398046511104 259 4398046511104
  true 1451121671591 4398046511104 1 844800000000
  (@p9510 p504 p9511 p2694
    19246474690605 4398046511104 259 4398046511104
    (p9518 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div 19246474690605 4398046511104)

noncomputable def p9520 :=
nat_lit 782488413335890925098809425920

noncomputable def p9521 :=
BSN.cos_reduce2
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 19246474690605)
    (@Nat.cast.{0} Real Real.instNatCast 4398046511104))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast p9520)
    (@Nat.cast.{0} Real Real.instNatCast p2704))
  226375608064910080 72057594037927936 false

noncomputable def p9522 :=
BSN.sin_reduce_arg_pos_rat_q2 19246474690605 4398046511104 226375608064910080
  72057594037927936 0 p9520 p2704 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p9523 :=
nat_lit
  3806082959624136141258961600693332918789974061754705422632334078636962327557383473404348520319895065798584442859575161569130362394363224010438366875984052041726166995541953484040544549806192955528882179041340805469432509524994090453867581052143636204610304081920000000

noncomputable def p9524 :=
nat_lit
  54647442126336236359399986423450561197650762062048385111553093505612816799198266906733366355560629165039021582688970114725801282869898626499257063401592963921372214307296811984611633666279743763531892148735153242315419469867201356677209128960000000000000000

noncomputable def p9525 :=
nat_lit
  38786301012292987969646187039466228131889907252630172372757672537928160452916910140605459837243575222554782199606471128018488203904326381847379772224411218169327630191210753484428642114423191572560505480396320789707382780687837016879745906675985222975504550723584000000

noncomputable def p9526 :=
BSN.cos_dyadic_bound_f 11119829158245280 9007199254740992 5 4
  4398046511104 1691250000001 p9523 p2708
  p9524 p9525 p2711

noncomputable def p9527 :=
@BSN.binarySplit_of_base4 (BSN.cosEvenP 11119829158245280) (BSN.cosEvenQ 9007199254740992)
  0 4 p9523 p2708 p9524
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p9528 :=
p9526 p9524 1451121671591 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p9527 (Eq.refl true))

noncomputable def p9529 :=
@BSN.binarySplit_of_base4 (BSN.cosOddP 11119829158245280) (BSN.cosOddQ 9007199254740992) 0
  4 p9525 p2711 p9524 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9530 :=
@BSN.cos_arg_round false 1451121671591 4398046511104 p9520
  p2704 11119829158245280 9007199254740992 1691250000001
  1689600000000
  (p9528 (p9529 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p9531 :=
p9521 1451121671591 4398046511104 0 1000000000000000
  1689600000000 844800000000 p9522 BSN.pi_near_15 p9530
  (Eq.refl true) (Eq.refl true)

noncomputable def p9532 :=
@p9421 1451121671591 4398046511104 3405780739
  56693568307200000000
  (@p9422 1451121671591 4398046511104 223201246511104
    p2689 1451121671591 4398046511104 3405780739
    56693568307200000000
    (p9519 (p9531 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p9533 :=
@p9420 1451121671591 4398046511104 3405780739
  56693568307200000000 6664779904053 6664779906481 2199023255552
  p9532 (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p9534 :=
@Enclosure.Real.IsNear.recentre' p9418 false 13329559810534 4398046511104
  2428 4398046511104 6664779905267 2199023255552 607
  1099511627776
  (p9533 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p9535 :=
nat_lit
  590611490391187310253820383118199102540221007795081056600567647535240059721199833173528822907659894814182301673307651428183283175

noncomputable def p9536 :=
@Enclosure.Real.IsNear.subLit_tt_n p9498
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p9499
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
        (Enclosure.sfrac false 12 1))))
  p9535 p9503

noncomputable def p9537 :=
nat_lit
  1503113071493838392556898850421529884485132544895425890259568263772834003521373100284868229789471626031752484775140618648466459707766237124738617345883581702492688184852040474631960891

noncomputable def p9538 :=
nat_lit 786608881533493974909807646299923470070584849445558610049136570001170721674206125

noncomputable def p9539 :=
nat_lit
  8865456631199360235595325039467265026681392364156701182398048821847258739663477738506691522205624298875183193641258161

noncomputable def p9540 :=
nat_lit
  69998221207921616402607868742381042965867162409178455905727938560000000000000000000000000000000000000000000000000000000000000

noncomputable def p9541 :=
nat_lit
  117062328390082921333481399933254212083455597040897570960273344238038545863119913592361060391977773355851101952888087946037932529223850042356571749724014893717922573272190924513953055963074182732861092659200

noncomputable def p9542 :=
@p9536 p9537 p9505 p9538 p2725
  p9539 p9540 p9541 p9502
  p9503 p9504 p9505

noncomputable def p9543 :=
@Enclosure.Real.IsNear.subLit_tf p9496
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 3 1) p9497)
    (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
        (Enclosure.sfrac false 12 1))))

noncomputable def p9544 :=
nat_lit
  431960780019419460530972815390870217105369830987428738470140733041666312408278249668884152484359804209218883985173843319844083175

noncomputable def p9545 :=
nat_lit
  1422280354128507552713569605468573983405932205699767552990965251818043289963255851762000251423976668588670056654159331396867533721283084015770684429748826987323995513783483981831960891

noncomputable def p9546 :=
nat_lit 2099724668596670574868242218826304059017143465056559318251378508492712758287968898789123159239589668371875

noncomputable def p9547 :=
nat_lit 71671831749689734737838152978190216899892655911508785116799651230841339877765150252188079784691427704832

noncomputable def p9548 :=
nat_lit
  324185486858570285683227753078743229477372993945875239600505351555359684019041340032991281618831369189555924782437685538037931288219072629132313311381

noncomputable def p9549 :=
nat_lit
  727225958124125266892007318182466655708418485156424353908608151758197951014787268739072000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p9550 :=
nat_lit
  42330207368750672354344843369494678578129031149243441838125354902306241159867215864578134132480497010813270385029804543786703182853402767971796862077349125720238938568559479244815131054701017392476418113508756016777888565120571801600

noncomputable def p9551 :=
@p9543 p9544 p9503 p9545 p9505
  p9546 p9547 p9548 p9549
  p9550 p9535 p9503

noncomputable def p9552 :=
@Enclosure.Real.IsNear.subLit_tf p9494
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 3 1) p9495)
    (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
        (Enclosure.sfrac false 12 1))))

noncomputable def p9553 :=
nat_lit 31334183568456515743308905836461461155541206493372300087173698753163450167144656177975089325

noncomputable def p9554 :=
nat_lit
  72051908380938374311598302013392905991586434491941661362613297654829231038639842529656639346897214437862866193729209101893

noncomputable def p9555 :=
nat_lit
  426754495766387448316781864683785734038475917992337947093374456020217628638603272530085042245882052434526125684805613137921676775

noncomputable def p9556 :=
nat_lit
  1418997989120495980710017233007449548619154949527178325732868786116130786969328196635449562780795539563136018034782470307746823788077354978352904085590494075707995513783483981831960891

noncomputable def p9557 :=
nat_lit
  14078714388241028647460229048521771731145525132975081569586507077259321731235033176115820036651877339815030156240375525748418538780925128250258778895432340969321802910325006420329754136478671642875791649424882134731980800

noncomputable def p9558 :=
@p9552 p9553 p7956 p9554 p7958
  p9555 p9503 p9556 p9505
  p9557 p9544 p9503

noncomputable def p9559 :=
@Enclosure.Real.IsNear.subLit_tt_n
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p9491
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p9411 (Enclosure.sfrac false 1 16)))))

noncomputable def p9560 :=
@p9559
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p9493
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 4 1) Real.pi))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p9411 (Enclosure.sfrac false 1 16)))))

noncomputable def p9561 :=
nat_lit 485088491796742404505328276561705909941556577914592325327425553475383065500456063326788606125

noncomputable def p9562 :=
nat_lit
  16922267453881654302546004741701678072007208814611490616909467803865321433277130631051296055963396910099922193729209101893

noncomputable def p9563 :=
nat_lit 666732032479531339709496790667782109596020526851043275

noncomputable def p9564 :=
nat_lit 2654395657118365759622908350104240344271700512428616578078363745920134591

noncomputable def p9565 :=
nat_lit
  1500609268604150484320074118944637098926285776103249156132389088121687154949621279709356827389235141582076636329989349709383642589691947620761600

noncomputable def p9566 :=
@p9560 p9561 p7956 p9562 p7958
  p9563 p5762 p9564 p5764
  p9565 p9553 p7956

noncomputable def p9567 :=
nat_lit 446204428728541122764518217766268326334607937140577624481088308582964802068510125

noncomputable def p9568 :=
@Enclosure.Real.IsNear.mulLit_ft p9491
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p9411 (Enclosure.sfrac false 1 16))))
  p9567

noncomputable def p9569 :=
nat_lit 1805110541663495218890802261109951971424477720759630467281581502372083299034824760659121810837237408719

noncomputable def p9570 :=
@p9568 p2761 p9569 p5163 1087144054529
  1099511627776 4016757557 28346784153600000000 p9561
  p7956 p9562 p7958

noncomputable def p9571 :=
@Enclosure.Real.IsNear.mulLit_ff p9490
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p9572 :=
nat_lit 583923451428549644710770238227670055200218299971428025

noncomputable def p9573 :=
nat_lit 51604136997645203626211660965473240699996229679606214676496136671

noncomputable def p9574 :=
nat_lit 764148841148470004476998805

noncomputable def p9575 :=
nat_lit 1106436514748425902878063839

noncomputable def p9576 :=
@p9571 p9572 p2767 p9573 p5168
  p9574 p976 p9575 p5171 p9567
  p2761 p9569

noncomputable def p9577 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p9578 :=
@p9577
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p9579 :=
@p9578 p9574 p976 p9575 p5171
  p9574 p976 p9575 p5171 p9572
  p2767 p9573

noncomputable def p9580 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
        (Enclosure.sfrac false 12 1)))
    (Enclosure.sfrac false 1 1))
  884279719003555

noncomputable def p9581 :=
@p9580 140737488355328 1 500000000000000 864148328551
  2199023255552 41 2199023255552 p9574 p976
  p9575 p5171

noncomputable def p9582 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 2 1)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
      (Enclosure.sfrac false 12 1)))
  (Enclosure.sfrac false 1 1) 3063171584103 2199023255552

noncomputable def p9583 :=
@p9582 41 2199023255552 1 1 0 1
  864148328551 864148328551 2199023255552 41 2199023255552

noncomputable def p9584 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 2 1)
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
    (Enclosure.sfrac false 12 1))
  2 1 0 1

noncomputable def p9585 :=
@p9584 3063171584103 4398046511104 41 4398046511104
  3063171584103 2199023255552 41 2199023255552
  (Enclosure.Real.IsNear.const false 2 1)
  (@p9512 1 3063171584103 3063171584103 4398046511104
    41 4398046511104 (p9517 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p9586 :=
@p9579 p5168
  (p9581 d144
    (p9583 (p9585 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (p9581 d144
    (p9583 (p9585 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))

noncomputable def p9587 :=
@p9576 p5163 (p9586 (Eq.refl true))
  (p9581 d144
    (p9583 (p9585 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p9588 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p9411 (Enclosure.sfrac false 1 16))))
  true

noncomputable def p9589 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p9411 (Enclosure.sfrac false 1 16)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Neg.neg.{0} Real Real.instNeg (@Nat.cast.{0} Real Real.instNatCast 118261103825))
    (@Nat.cast.{0} Real Real.instNatCast 68719476736))
  true

noncomputable def p9590 :=
nat_lit 4684804976482199565335788133537547896845

noncomputable def p9591 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p9411 (Enclosure.sfrac false 1 16)))
  true p9590

noncomputable def p9592 :=
nat_lit 2328907284556250359231104694779001220053

noncomputable def p9593 :=
nat_lit 5297876764335658831771279

noncomputable def p9594 :=
nat_lit 4088950944721029657065103

noncomputable def p9595 :=
@p9454 (Enclosure.sfrac false 1 16) p9594
  p2793 431499976853391 p2793 1 16 0

noncomputable def p9596 :=
nat_lit 84766028229370541308340464

noncomputable def p9597 :=
nat_lit 9383020153656082402314609

noncomputable def p9598 :=
@Enclosure.Real.IsNear.subLit_ff_n
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
      (Enclosure.sfrac false 12 1))
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
      (Enclosure.sfrac false 12 1)))
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
    (Enclosure.sfrac false 12 1))
  p9597

noncomputable def p9599 :=
nat_lit 17983396436505729249833689833340403712

noncomputable def p9600 :=
@p9598 p2793 251180069898127 p2793
  3063171584103 4398046511104 41 4398046511104 p9599
  p9594 p2793 431499976853391

noncomputable def p9601 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
    (Enclosure.sfrac false 12 1))
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
    (Enclosure.sfrac false 12 1))
  3063171584103 4398046511104 41

noncomputable def p9602 :=
@p9601 4398046511104 3063171584103 4398046511104 41
  4398046511104 p9597 p2793 251180069898127
  p2793
  (@p9512 1 3063171584103 3063171584103 4398046511104
    41 4398046511104 (p9517 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p9603 :=
p9602
  (@p9512 1 3063171584103 3063171584103 4398046511104
    41 4398046511104 (p9517 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p9604 :=
@p9600 p2793 (p9603 (Eq.refl true))
  (@p9512 1 3063171584103 3063171584103 4398046511104
    41 4398046511104 (p9517 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p9605 :=
@p9453 500000000000000 p9593 p2793
  431499976853391 p2793 p9590 p2789
  p9592 p5189 d144
  (@p9595 1 p9596 p9593 p2793
    431499976853391 p2793
    (p9604 (Eq.refl true) (Eq.refl true))
    (Enclosure.Real.IsNear.const false 1 16) (Eq.refl true)
    (Eq.refl true))

noncomputable def p9606 :=
@p9589 118261103825 68719476736 309 2199023255552 true
  2174288109058 2199023255552 1 844800000000
  (@p9591 p2789 p9592 p5189
    118261103825 68719476736 309 2199023255552
    (p9605 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_true_div 118261103825 68719476736)

noncomputable def p9607 :=
nat_lit
  6448691197534758682928889831883648996136981886169733585416804256271448790476712481161668650062141970086448240501511804462251643206660813871192960507079226409621726452392026370910712890625

noncomputable def p9608 :=
nat_lit
  87972314389919681436536573358802488508909229447352760535897166083252396451397479444074537888040383657117614823310149345001055593919431144202692571536365889716811725392947079355937325056000

noncomputable def p9609 :=
nat_lit
  1463763295272637422966616830364145143653230732311674894222235361942867170680626461422495969192311138049552375290308728652797298277790357079990086888732656859792768955230712890625

noncomputable def p9610 :=
nat_lit
  52416829153158150890635552302359824075332836578414610459368748782803310092399201888181567189424785058211894038420466603372813988664113702337495362279673676030708410033734836482910712890625

noncomputable def p9611 :=
nat_lit
  5014421920225421841882584681451741845007826078499107350546138466745386597729656328312248659618301868455704044928678512665060168853407575219553476577572855713858268347397983523288427528192000

noncomputable def p9612 :=
BSN.sin_dyadic_bound_f 118261103825 68719476736 5 4 2199023255552
  844800000000 p9607 p9608 p9609 p9610
  p9611

noncomputable def p9613 :=
@BSN.binarySplit_of_base4 (BSN.sinEvenP 118261103825) (BSN.sinEvenQ 68719476736) 0
  4 p9607 p9608 p9609 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9614 :=
p9612 p9609 2174288109058 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p9613 (Eq.refl true))

noncomputable def p9615 :=
@BSN.binarySplit_of_base4 (BSN.sinOddP 118261103825) (BSN.sinOddQ 68719476736) 0
  4 p9610 p9611 p9609 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9616 :=
p9606
  (BSN.sin_neg_of_bound 118261103825 68719476736 false 2174288109058
    2199023255552 1 844800000000
    (p9614 (p9615 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p9617 :=
p9570 p9587
  (@p9588 2174288109058 2199023255552 263242223255552
    p3422 1087144054529 1099511627776 4016757557
    28346784153600000000 (p9616 (Eq.refl true))
    (Eq.refl true))

noncomputable def p9618 :=
nat_lit 2027163967582983725907396168343954577255325

noncomputable def p9619 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p9493
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 4 1) Real.pi))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p9411 (Enclosure.sfrac false 1 16))))
  p9618

noncomputable def p9620 :=
nat_lit 89575738618064128810634563192674961445518198673052939

noncomputable def p9621 :=
@p9619 p2820 p9620 p5216 328898916487
  2199023255552 4016757557 28346784153600000000 p9563
  p5762 p9564 p5764

noncomputable def p9622 :=
nat_lit 2292446523445410013430996415

noncomputable def p9623 :=
nat_lit 3319309544245277708634191517

noncomputable def p9624 :=
@Enclosure.Real.IsNear.mulLit_ff p9493
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 4 1) Real.pi)
  p9622 p976 p9623 p5171

noncomputable def p9625 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 3 1)
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p9626 :=
@p9625 3 1 0 1 p9574 p976
  p9575 p5171 p9622 p976 p9623

noncomputable def p9627 :=
@p9626 p5171 (Enclosure.Real.IsNear.const false 3 1)
  (p9581 d144
    (p9583 (p9585 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p9628 :=
@p9624 884279719003555 70368744177664 1 250000000000000
  p9618 p2820 p9620 p5216
  p9627 d146 (Eq.refl true)

noncomputable def p9629 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p9411 (Enclosure.sfrac false 1 16)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Neg.neg.{0} Real Real.instNeg (@Nat.cast.{0} Real Real.instNatCast 118261103825))
    (@Nat.cast.{0} Real Real.instNatCast 68719476736))
  true

noncomputable def p9630 :=
@p9629 118261103825 68719476736 309 2199023255552 true
  328898916487 2199023255552 1 844800000000
  (@p9591 p2789 p9592 p5189
    118261103825 68719476736 309 2199023255552
    (p9605 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_true_div 118261103825 68719476736)

noncomputable def p9631 :=
nat_lit
  1901066612201251661887430790142570471334580896557488928325051269435500288925255867892041619014764269303265612145419427312989840373569833798907102748169351849597990174781256430430712890625

noncomputable def p9632 :=
nat_lit
  5174842022936451849208033726988381676994660555726632972699833299014846850082204673180855169884728450418683224900597020294179740818790067306040739502139169983341866199585122315055136768000

noncomputable def p9633 :=
nat_lit
  19323677205652179834370199288367938454452036558520959338157585896803045521501549142052708611805781511405573562225348304493242712795009260710120721800587391894719758120048141202270712890625

noncomputable def p9634 :=
nat_lit
  791750829509277132928829160229222396580183065026174844823074494749271568062577314996670840992363452914058533409791344105009500345274880297824233143827293007451305528536523714203435925504000

noncomputable def p9635 :=
BSN.cos_dyadic_bound_t 118261103825 68719476736 5 4 2199023255552
  844800000000 p9631 p9632 p9609 p9633
  p9634

noncomputable def p9636 :=
@BSN.binarySplit_of_base4 (BSN.cosEvenP 118261103825) (BSN.cosEvenQ 68719476736) 0
  4 p9631 p9632 p9609 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9637 :=
p9635 p9609 328898916487 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p9636 (Eq.refl true))

noncomputable def p9638 :=
@BSN.binarySplit_of_base4 (BSN.cosOddP 118261103825) (BSN.cosOddQ 68719476736) 0
  4 p9633 p9634 p9609 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9639 :=
p9630
  (BSN.cos_neg_of_bound 118261103825 68719476736 true 328898916487
    2199023255552 1 844800000000
    (p9637 (p9638 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p9640 :=
p9621 p9628
  (@p9446 328898916487 2199023255552 263242223255552
    p3422 328898916487 2199023255552 4016757557
    28346784153600000000 (p9639 (Eq.refl true))
    (Eq.refl true))

noncomputable def p9641 :=
nat_lit 1376741857092652684294050915

noncomputable def p9642 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 3 1) p9495)
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
      (Enclosure.sfrac false 12 1)))
  p9641

noncomputable def p9643 :=
nat_lit 91909115571459509268378040599126613

noncomputable def p9644 :=
nat_lit 309974229059607580400913328729786792210867044044235249463334590970802047471394270082869914194557920685

noncomputable def p9645 :=
nat_lit
  981879273199766784623453190803153568694296331036857634254058176279720564062887279999003745687558882249798594058730899362217562362586979207

noncomputable def p9646 :=
@p9642 p3406 p9643 p2846 p9644
  p2848 p9645 p5842 p9555
  p9503 p9556 p9505

noncomputable def p9647 :=
nat_lit 458913952364217561431350305

noncomputable def p9648 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 3 1) p9495
  3 1 0 1 p9647 p3406

noncomputable def p9649 :=
@Enclosure.Real.IsNear.neg
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
          (Enclosure.sfrac false 12 1)))))

noncomputable def p9650 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
        (Enclosure.sfrac false 12 1))))
  884279719003555

noncomputable def p9651 :=
@p9650 140737488355328 1 500000000000000 518969215851
  549755813888 3405780739 56693568307200000000 p9647
  p3406 p9643 p2854

noncomputable def p9652 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
        (Enclosure.sfrac false 12 1))))
  true

noncomputable def p9653 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
      (Enclosure.sfrac false 12 1)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 19246474690605)
    (@Nat.cast.{0} Real Real.instNatCast 4398046511104))
  false

noncomputable def p9654 :=
@p9653 19246474690605 4398046511104 259 4398046511104
  true 4151753726808 4398046511104 1 844800000000
  (@p9510 p504 p9511 p2694
    19246474690605 4398046511104 259 4398046511104
    (p9518 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div 19246474690605 4398046511104)

noncomputable def p9655 :=
BSN.sin_reduce2
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 19246474690605)
    (@Nat.cast.{0} Real Real.instNatCast 4398046511104))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast p9520)
    (@Nat.cast.{0} Real Real.instNatCast p2704))
  226375608064910080 72057594037927936 false

noncomputable def p9656 :=
nat_lit
  34398793957127708149125891601415919212559416664570510210683201578983407859379245660400439538907397335786830207583318536749740578071480597708710227395134637353506259092741022175124096984155580006400000

noncomputable def p9657 :=
nat_lit
  3574187890767031593137997599211478341782927521150170947507211741275007988988560650934768744483435795002952926077017622755349212873827579152433495830804383579096629586340152046780416000000000000

noncomputable def p9658 :=
nat_lit
  171912344711349572706909774490939246527523283716378472568871348051723148799166826938671406894499474872086131923147522142701365578694618098647496782541296767240489432564722799377373709259644076032000000

noncomputable def p9659 :=
BSN.sin_dyadic_bound_f 11119829158245280 9007199254740992 4 3
  4398046511104 1691250000001 p9656 p2863
  p9657 p9658 p2866

noncomputable def p9660 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 11119829158245280) (BSN.sinEvenQ 9007199254740992)
  0 3 p9656 p2863 p9657
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p9661 :=
p9659 p9657 4151753726808 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p9660 (Eq.refl true))

noncomputable def p9662 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 11119829158245280) (BSN.sinOddQ 9007199254740992) 0
  3 p9658 p2866 p9657 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9663 :=
@BSN.sin_arg_round false 4151753726808 4398046511104 p9520
  p2704 11119829158245280 9007199254740992 1691250000001
  1689600000000
  (p9661 (p9662 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p9664 :=
p9655 4151753726808 4398046511104 0 1000000000000000
  1689600000000 844800000000 p9522 BSN.pi_near_15 p9663
  (Eq.refl true) (Eq.refl true)

noncomputable def p9665 :=
p9651 d144
  (@p9652 4151753726808 4398046511104 223201246511104
    p2689 518969215851 549755813888 3405780739
    56693568307200000000
    (p9654 (p9664 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p9666 :=
@Neg.neg.{0} Real Real.instNeg
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p9490
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p9411 (Enclosure.sfrac false 1 16)))))

noncomputable def p9667 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9666
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 4 1) Real.pi)
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p9411 (Enclosure.sfrac false 1 16)))))

noncomputable def p9668 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9667
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) p9495)
    (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
        (Enclosure.sfrac false 12 1))))

noncomputable def p9669 :=
@Enclosure.Real.IsNear.of_eq
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
      (Enclosure.sfrac false 12 1)))
  (p9410
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9668
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p9497
        (Zeta.RiemannSiegel.correction
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
            (Enclosure.sfrac false 12 1))))))

noncomputable def p9670 :=
@p9414
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9668
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p9497
      (Zeta.RiemannSiegel.correction
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
          (Enclosure.sfrac false 12 1)))))
  6664779905267

noncomputable def p9671 :=
nat_lit 46509297150929637197316437953415552929246369676198102262731764983415857634509872999993055

noncomputable def p9672 :=
nat_lit
  147053180640154119824822792659273373072492704503645204891366196718111210655188728330787871841026286720832581602714993548106647

noncomputable def p9673 :=
@p9670 2199023255552 607 1099511627776 p9671
  p5269 p9672 p3512 p9644
  p2848 p9645 p5842

noncomputable def p9674 :=
nat_lit 141427180290724361209784967098334006754977492997994198393529663592856333391501308783456545

noncomputable def p9675 :=
@Enclosure.Real.IsNear.subLit_ff_n p9668
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p9497
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
        (Enclosure.sfrac false 12 1))))
  p9674 p5269

noncomputable def p9676 :=
nat_lit
  139185148107270071878770588289983656802306594218762785082989562168409247162973870092242158956817717548455605864467415948106647

noncomputable def p9677 :=
nat_lit 2487318568499929949403424429253006030202480620255936735632744260475

noncomputable def p9678 :=
nat_lit 504885059501628248632341013728370408020067550028913687894841605681016155331457736772393902757

noncomputable def p9679 :=
nat_lit
  19592002667433190926284902392011650249162865345643411798412349745158906908936570808728511857963244649665417441311737244468297631485442389182206953044049920

noncomputable def p9680 :=
@p9675 p9676 p3512 p9677 p5875
  p9678 p5877 p9679 p9671
  p5269 p9672 p3512

noncomputable def p9681 :=
@Enclosure.Real.IsNear.subLit_ff_p p9667
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) p9495)
    (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
        (Enclosure.sfrac false 12 1))))

noncomputable def p9682 :=
nat_lit 2809066668375649061563266906895340842724220936866929931371865678735

noncomputable def p9683 :=
nat_lit 6905809571197254306382961418096053500772922833925667508876186650291053622579062041497

noncomputable def p9684 :=
nat_lit 283066972761546547475878337122090357619978607638827876665344492053469711501161320271089375

noncomputable def p9685 :=
nat_lit
  136410600402465742485845599001627047707460117638090438993177589012854564951296943877651697817291199209644275304467415948106647

noncomputable def p9686 :=
nat_lit
  29788040921276772612599812127823567740622450778112183747457471007342572724021287464497361246543407041400507148770494973800275171796403276451423807854346240

noncomputable def p9687 :=
@p9681 p9682 p5882 p9683 p5892
  p9684 p5269 p9685 p3512
  p9686 p9674 p5269

noncomputable def p9688 :=
@Enclosure.Real.IsNear.subLit_ft p9666
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 4 1) Real.pi)
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p9411 (Enclosure.sfrac false 1 16)))))

noncomputable def p9689 :=
nat_lit 192051790486199350443261141852287548377887278706471820480606348175

noncomputable def p9690 :=
nat_lit 801061397136251202950121679325315167334361077067958425307491219410553874193020680499

noncomputable def p9691 :=
nat_lit 961339439055289594464850595

noncomputable def p9692 :=
nat_lit 108396763091157798252210137709133619

noncomputable def p9693 :=
nat_lit 217341006362762705247059611760857274559977523526052902430143567690918934985043266075927511040

noncomputable def p9694 :=
@p9688 p9689 p5882 p9690 p5884
  p9691 p3406 p9692 p3486
  p9693 p9682 p5882

noncomputable def p9695 :=
@Enclosure.Real.IsNear.neg
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p9490
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p9411 (Enclosure.sfrac false 1 16)))))

noncomputable def p9696 :=
@Enclosure.Real.IsNear.mulLit_ft p9490
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p9411 (Enclosure.sfrac false 1 16))))
  p9572

noncomputable def p9697 :=
@p9696 p2767 p9573 p5168 328898916487
  2199023255552 4016757557 28346784153600000000 p9689
  p5882 p9690 p5884

noncomputable def p9698 :=
p9697 (p9586 (Eq.refl true))
  (@p9446 328898916487 2199023255552 263242223255552
    p3422 328898916487 2199023255552 4016757557
    28346784153600000000 (p9639 (Eq.refl true))
    (Eq.refl true))

noncomputable def p9699 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 4 1) Real.pi)
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p9411 (Enclosure.sfrac false 1 16))))
  884279719003555

noncomputable def p9700 :=
@p9699 70368744177664 1 250000000000000 1087144054529
  1099511627776 4016757557 28346784153600000000 p9691
  p3406 p9692 p3486

noncomputable def p9701 :=
p9700 d146
  (@p9588 2174288109058 2199023255552 263242223255552
    p3422 1087144054529 1099511627776 4016757557
    28346784153600000000 (p9616 (Eq.refl true))
    (Eq.refl true))

noncomputable def p9702 :=
@p9687 p9676 p3512
  (@p9694 p9683 p5892
    (@p9695 true p9689 p5882 p9690
      p5884 (p9698 (Eq.refl true)))
    (p9701 (Eq.refl true)) (Eq.refl true) (Eq.refl true))

noncomputable def p9703 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 2 1) p9495)
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
      (Enclosure.sfrac false 12 1)))
  p9647

noncomputable def p9704 :=
nat_lit 616819278000269066125002442329315791211044025396423137058245375

noncomputable def p9705 :=
nat_lit 94052082685536123137823350448657309218309967572880297323909762784039292113108269

noncomputable def p9706 :=
nat_lit 8344438220014764833761199562833433504804034520289713848320000000000000000000000000000000

noncomputable def p9707 :=
@p9703 p5295 p9643 p2908 p9704
  p5309 p9705 p9706 p9684
  p5269 p9685 p3512

noncomputable def p9708 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 2 1) p9495
  2 1 0 1 p9647 p3406

noncomputable def p9709 :=
@Neg.neg.{0} Real Real.instNeg
  (p9489
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p9411 (Enclosure.sfrac false 1 16)))))

noncomputable def p9710 :=
@Enclosure.Real.IsNear.of_eq
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
      (Enclosure.sfrac false 12 1)))
  (p9410
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9709
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p9495
        (Zeta.RiemannSiegel.correction
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
            (Enclosure.sfrac false 12 1))))))

noncomputable def p9711 :=
@p9414
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9709
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p9495
      (Zeta.RiemannSiegel.correction
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
          (Enclosure.sfrac false 12 1)))))
  6664779905267

noncomputable def p9712 :=
nat_lit 92549084406045132646970491655354171810278926461125

noncomputable def p9713 :=
nat_lit 13940831085008763599735452878322399086066358749415089178181545397249

noncomputable def p9714 :=
nat_lit 3794611175187476343926937062330322762501980160000000000000000000000000000000

noncomputable def p9715 :=
@p9711 2199023255552 607 1099511627776 p9712
  p2930 p9713 p9714 p9704
  p5309 p9705 p9706

noncomputable def p9716 :=
nat_lit 830739869429784433532063262989187837845

noncomputable def p9717 :=
@Enclosure.Real.IsNear.subLit_ff_n p9709
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p9495
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
        (Enclosure.sfrac false 12 1))))
  p9716 p8122

noncomputable def p9718 :=
nat_lit 20780300287100937777154361860835000268199225533

noncomputable def p9719 :=
nat_lit 44621301128033674932683952829235200000000000000000000000

noncomputable def p9720 :=
nat_lit 1005957230501209116096595447032406066887456812443845

noncomputable def p9721 :=
nat_lit 12173667024352436419340036259628885703865834080375178436575145397249

noncomputable def p9722 :=
nat_lit 31492821498054754027740329656020044753449721232521067205388206388932963487482692763648000

noncomputable def p9723 :=
@p9717 p9718 p9719 p9720 p2930
  p9721 p9714 p9722 p9712
  p2930 p9713 p9714

noncomputable def p9724 :=
@Enclosure.Real.IsNear.neg
  (p9489
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p9411 (Enclosure.sfrac false 1 16)))))

noncomputable def p9725 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p9726 :=
@p9725
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p9411 (Enclosure.sfrac false 1 16))))
  p9574

noncomputable def p9727 :=
@p9726 p976 p9575 p5171 1087144054529
  1099511627776 4016757557 28346784153600000000 p9716
  p8122 p9718 p9719

noncomputable def p9728 :=
p9727
  (p9581 d144
    (p9583 (p9585 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (@p9588 2174288109058 2199023255552 263242223255552
    p3422 1087144054529 1099511627776 4016757557
    28346784153600000000 (p9616 (Eq.refl true))
    (Eq.refl true))

noncomputable def p9729 :=
@Enclosure.Real.IsNear.mulLit_ff p9495
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
      (Enclosure.sfrac false 12 1)))
  p9647 p3406 p9643

noncomputable def p9730 :=
nat_lit 2192038889466646804437029

noncomputable def p9731 :=
@p9414
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p9411 (Enclosure.sfrac false 1 16))))
  6664779905267

noncomputable def p9732 :=
@p9731 2199023255552 607 1099511627776 328898916487
  2199023255552 4016757557 28346784153600000000 p9730
  p5932 31917816145842354558167 p3576

noncomputable def p9733 :=
p9732
  (p9507
    (@Enclosure.Real.IsNear.neg p9418 false 6664779905267 2199023255552
      607 1099511627776 (p9534 (Eq.refl true))))
  (@p9446 328898916487 2199023255552 263242223255552
    p3422 328898916487 2199023255552 4016757557
    28346784153600000000 (p9639 (Eq.refl true))
    (Eq.refl true))

noncomputable def p9734 :=
@p9729 p2854 p9730 p5932
  31917816145842354558167 p3576 p9720 p2930
  p9721 p9714
  (@p9649 true p9647 p3406 p9643
    p2854 (p9665 (Eq.refl true)))
  (@p9412 false p9730 p5932 31917816145842354558167
    p3576
    (BSN.correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
        (Enclosure.sfrac false 12 1))
      (p9413 (Eq.refl true) (Eq.refl true)
        (p9193 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p9733 (Eq.refl true)))

noncomputable def p9735 :=
p9715
  (p9507
    (@Enclosure.Real.IsNear.neg p9418 false 6664779905267 2199023255552
      607 1099511627776 (p9534 (Eq.refl true))))
  (p9723
    (@p9724 true p9716 p8122 p9718
      p9719 (p9728 (Eq.refl true)))
    (p9734 (Eq.refl true)) (Eq.refl true) (Eq.refl true))

noncomputable def p9736 :=
p9707
  (@p9708 p9643 p2854 p9647
    p5295 p9643 p2908
    (Enclosure.Real.IsNear.const false 2 1)
    (@p9649 true p9647 p3406 p9643
      p2854 (p9665 (Eq.refl true)))
    (Eq.refl true))
  (@p9710 false p9704 p5309 p9705
    p9706
    (BSN.deriv_correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
        (Enclosure.sfrac false 12 1))
      (p9413 (Eq.refl true) (Eq.refl true)
        (p9193 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p9735 (Eq.refl true)))

noncomputable def p9737 :=
nat_lit 1134705492887094147338604997577388798847775

noncomputable def p9738 :=
nat_lit 2480262589855468650969998491595534020076555544942228141418771

noncomputable def p9739 :=
@Enclosure.Real.IsNear.mulLit_ff p9497
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
      (Enclosure.sfrac false 12 1)))
  p9737 p5940 p9738

noncomputable def p9740 :=
@Enclosure.Real.IsNear.neg
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 4 1)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
          (Enclosure.sfrac false 12 1)))))

noncomputable def p9741 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 4 1)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
        (Enclosure.sfrac false 12 1))))
  p1068

noncomputable def p9742 :=
@p9741 p1070 p1071 p1072 1451121671591
  4398046511104 3405780739 56693568307200000000 p9737
  p5940 p9738 p2961

noncomputable def p9743 :=
p9742 d148
  (@p9422 1451121671591 4398046511104 223201246511104
    p2689 1451121671591 4398046511104 3405780739
    56693568307200000000
    (p9519 (p9531 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p9744 :=
@p9739 p2961 p9730 p5932
  31917816145842354558167 p3576 p9677 p5875
  p9678 p5877
  (@p9740 true p9737 p5940 p9738
    p2961 (p9743 (Eq.refl true)))
  (@p9412 false p9730 p5932 31917816145842354558167
    p3576
    (BSN.correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
        (Enclosure.sfrac false 12 1))
      (p9413 (Eq.refl true) (Eq.refl true)
        (p9193 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p9733 (Eq.refl true)))

noncomputable def p9745 :=
p9673
  (p9507
    (@Enclosure.Real.IsNear.neg p9418 false 6664779905267 2199023255552
      607 1099511627776 (p9534 (Eq.refl true))))
  (p9680
    (p9702 (p9736 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true))
    (p9744 (Eq.refl true)) (Eq.refl true) (Eq.refl true))

noncomputable def p9746 :=
p9646
  (@p9648 p9643 p2854 p9641
    p3406 p9643 p2846
    (Enclosure.Real.IsNear.const false 3 1)
    (@p9649 true p9647 p3406 p9643
      p2854 (p9665 (Eq.refl true)))
    (Eq.refl true))
  (@p9669 false p9644 p2848 p9645
    p5842
    (BSN.iteratedDeriv_two_correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
        (Enclosure.sfrac false 12 1))
      (p9413 (Eq.refl true) (Eq.refl true)
        (p9193 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p9745 (Eq.refl true)))

noncomputable def p9747 :=
@p9558 p9545 p9505
  (@p9566 p9554 p7958
    (p9617 (Eq.refl true)) (p9640 (Eq.refl true))
    (Eq.refl true) (Eq.refl true))
  (p9746 (Eq.refl true)) (Eq.refl true) (Eq.refl true)

noncomputable def p9748 :=
nat_lit 3404116478661282442015814992732166396543325

noncomputable def p9749 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 3 1) p9497)
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
      (Enclosure.sfrac false 12 1)))
  p9748

noncomputable def p9750 :=
@p9749 p5940 p9738 p2972 p9704
  p5309 p9705 p9706 p9546
  p9547 p9548 p9549

noncomputable def p9751 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 3 1) p9497
  3 1 0 1 p9737 p5940

noncomputable def p9752 :=
p9750
  (@p9751 p9738 p2961 p9748
    p5940 p9738 p2972
    (Enclosure.Real.IsNear.const false 3 1)
    (@p9740 true p9737 p5940 p9738
      p2961 (p9743 (Eq.refl true)))
    (Eq.refl true))
  (@p9710 false p9704 p5309 p9705
    p9706
    (BSN.deriv_correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
        (Enclosure.sfrac false 12 1))
      (p9413 (Eq.refl true) (Eq.refl true)
        (p9193 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p9735 (Eq.refl true)))

noncomputable def p9753 :=
nat_lit 358848050239148233919517238414820679771156219578388347625

noncomputable def p9754 :=
nat_lit 66933323626607239274657392503976030531320562242561253490413465518802954402219710479557

noncomputable def p9755 :=
@Enclosure.Real.IsNear.mulLit_tf p9499
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
      (Enclosure.sfrac false 12 1)))
  p9753 p5362 p9754

noncomputable def p9756 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 8 1)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi) Real.pi))
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
        (Enclosure.sfrac false 12 1))))

noncomputable def p9757 :=
@p9756 p1059 p1061 p1062 p1063
  518969215851 549755813888 3405780739 56693568307200000000
  p9753 p5362 p9754

noncomputable def p9758 :=
@p9757 p2980 d149
  (@p9652 4151753726808 4398046511104 223201246511104
    p2689 518969215851 549755813888 3405780739
    56693568307200000000
    (p9654 (p9664 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p9759 :=
@p9755 p2980 p9730 p5932
  31917816145842354558167 p3576 p9538 p2725
  p9539 p9540 (p9758 (Eq.refl true))
  (@p9412 false p9730 p5932 31917816145842354558167
    p3576
    (BSN.correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
        (Enclosure.sfrac false 12 1))
      (p9413 (Eq.refl true) (Eq.refl true)
        (p9193 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p9733 (Eq.refl true)))

noncomputable def p9760 :=
p9506
  (p9507
    (@Enclosure.Real.IsNear.neg p9418 false 6664779905267 2199023255552
      607 1099511627776 (p9534 (Eq.refl true))))
  (p9542
    (@p9551 p9537 p9505 p9747
      (p9752 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true))
    (p9759 (Eq.refl true)) (Eq.refl true) (Eq.refl true))

noncomputable def p9761 :=
@p9488 p9481
  (@p9500 false p9485 p9486 p9487
    p3309
    (BSN.iteratedDeriv_three_correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
        (Enclosure.sfrac false 12 1))
      (p9413 (Eq.refl true) (Eq.refl true)
        (p9193 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p9760 (Eq.refl true)))

noncomputable def p9762 :=
@p9479 p9480 p9481 1353120155 17179869184
  1 17179869184 p9405 p9382 p9406
  p9407
  (@p9483 p9478 p9480 p9481
    (BSN.correctionLinear_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9190
        (Enclosure.sfrac false 12 1)))
    (@Enclosure.Real.IsNear.neg p9482 false p9477 p9478
      p9480 p9481
      (p9761 d150 (Eq.refl true))))

noncomputable def p9763 :=
@Enclosure.Real.IsNear.recentre' (@Inv.inv.{0} Real Real.instInv p9190) false
  1353120155 17179869184 1 17179869184 1353120155
  17179869184

noncomputable def p9764 :=
@Enclosure.Real.IsNear.inv_image p9190 54530986059 4294967296 5
  2147483648 676560077 676560078 8589934592
  (p9399 (Eq.refl true)) (Eq.refl true) (Eq.refl true)

noncomputable def p9765 :=
p9476
  (p9762
    (@p9763 1 17179869184
      (p9764 (Eq.refl true) (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true))
    (Eq.refl true))

noncomputable def p9766 :=
@p9384 p9185
  (@p9386 17179869184
    (@p2563 1 0 1
      (BSN.neg_one_pow_even_mk 12 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1))
    p9402 (Eq.refl true))
  (p9765 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p9767 :=
@p9192 p9182 p9184 p9185
  (BSN.hardyZApproximantRS_eq
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
      true 5)
    12
    (p9193 (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (p9379 p9766 (Eq.refl true) (Eq.refl true))

theorem d184 : p9183 p9184 p9185 :=
@p9186 p9182 p9184 p9185
  (@Eq.refl.{1} Real
    (hardyZApproximantRS
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
        true 5)))
  p9767

noncomputable def p9768 :=
nat_lit
  6755439337148954750570065882083003057665797093852252582475402571189652490573031811940838025103950943787133983951362051737491166658325251020116999006223631040628568348864385095

noncomputable def p9769 :=
nat_lit
  1978643211784836272484020168157177520281050792809694719312504448743177800852254937362531208489944359916781371408129114714810920274454009679740369240815145343332854177189593088

noncomputable def p9770 :=
Enclosure.Real.IsNear
  (hardyZApproximantRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
      true 5))
  true p9768 p9769

noncomputable def p9771 :=
nat_lit
  46216411663348696503858520206061622319620792125645443934767531176640354228117947006846082425468563254692557636836594958646299486127559872174038303518949672233594855847749554147103235107968790241618511794397650586121238367164969

noncomputable def p9772 :=
nat_lit
  14377713567062223935658933105375863756281156858834953474847460676088648473948252047413787226523068829453839582693482099893784955926492411908134891730816204800000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p9773 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZApproximantRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
      true 5))
  (hardyZApproximantRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
      true 5))
  true p9768

noncomputable def p9774 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
  (Zeta.RiemannSiegel.mainSumOfPhase
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
      true 5)
    12)

noncomputable def p9775 :=
@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p9776 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (@HPow.hPow.{0, 0, 0} Real Nat Real
    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
    (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)))
    12)
  (p9775
    (@Neg.neg.{0} Real Real.instNeg
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
        (@OfNat.ofNat.{0} Real 4
          (@instOfNatAtLeastTwo.{0} Real 4 Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))))))

noncomputable def p9777 :=
Real.sqrt
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p9778 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p9776
  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
        (Enclosure.sfrac false 12 1)))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Zeta.RiemannSiegel.correctionLinear
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
          (Enclosure.sfrac false 12 1)))
      (@Inv.inv.{0} Real Real.instInv p9777)))

noncomputable def p9779 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZApproximantRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
      true 5))
  (p9774 p9778) true p9768

noncomputable def p9780 :=
@BSN.floor_sqrt_eq_dec
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
    true 5)
  101408700 100000 12
  (Enclosure.sfrac_ofScientific_eq 101408700 5 100000 (Eq.refl true))

noncomputable def p9781 :=
@Enclosure.Real.IsNear.subLit_tf
  (Zeta.RiemannSiegel.mainSumOfPhase
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
      true 5)
    12)

noncomputable def p9782 :=
nat_lit
  254512722021031626832092503662145880679919752982511584940474549842601163477292060897588023604558370802500181280565452143682193296387426206937346168069446856529089019066028103

noncomputable def p9783 :=
nat_lit
  635657947589277949038397113297367917016605366734112820847169783528760867615436292655282161447236729172648154636809981567624351681351952476549425541349672233594855847749554147103235107968790241618511794397650586121238367164969

noncomputable def p9784 :=
nat_lit
  464230256370666856548516325121790247842281609853876279962614348283101908169857918909656345674475140863265197546260621869887752606182280948198290381206319932509922373466772043554797649920

noncomputable def p9785 :=
@p9781 p9778 225781117399 68719476736 217857
  68719476736 p9782 p9769 p9783 p9772
  p9784 p9768

noncomputable def p9786 :=
@Enclosure.Real.IsNear.of_eq
  (Zeta.RiemannSiegel.mainSumOfPhase
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
      true 5)
    12)

noncomputable def p9787 :=
@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
      true 5)
    12)

noncomputable def p9788 :=
p9787
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
      true 5)
    12)

noncomputable def p9789 :=
@p9786 p9788 true 225781117399 68719476736 217857
  68719476736
  (BSN.main_sum_of_phase_eq
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
      true 5)
    12)

noncomputable def p9790 :=
@Enclosure.Real.IsNear.addLit_tt
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
      true 5)
    12)

noncomputable def p9791 :=
@p9790
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
      true 5)
    12)

noncomputable def p9792 :=
@p9791 225781117399 137438953472 217857 137438953472
  225781117399 137438953472 217857 137438953472
  62062240978114661318656 225781117399 68719476736

noncomputable def p9793 :=
BSN.mainSumRS_step
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
      true 5))
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
    true 5)
  Real.cos BSN.quadSignNeg

noncomputable def p9794 :=
p9793 11 12 101408700 100000 286
  137438953472 68719476736 2305843009213693952 false 284540620532287
  3360

noncomputable def p9795 :=
p9794 341522969406 43 39675208392 8 true
  188625310068 204289 true 49242407842 7244019458077122842 1

noncomputable def p9796 :=
p9795 false 128711492185 true true 225781117399 217857
  BSN.abs_quadSignNeg (BSN.cos_quad_nat2 286 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 128711492185 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101408700 5 100000 (Eq.refl true))
  (Eq.refl true)

noncomputable def p9797 :=
BSN.mainSumRS_step2
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
      true 5))
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
    true 5)
  Real.cos Real.cos

noncomputable def p9798 :=
p9797 BSN.quadSignPos BSN.quadSignNeg 9 10 11 101408700
  100000 168 230 137438953472 68719476736

noncomputable def p9799 :=
p9798 2305843009213693952 false 284540620532287 3360
  316464885454 43 43462013224 8 329564216814 43
  41439403656

noncomputable def p9800 :=
p9799 8 true 176914781387 175257 true 113020413348
  true 11788651330 7244019458077122842 1 false

noncomputable def p9801 :=
p9800 93529202680 false false 136933685080 true true
  188625310068 204289 BSN.abs_quadSignPos
  (BSN.cos_quad_nat0 168 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 93529202680 137438953472)

noncomputable def p9802 :=
p9797 BSN.quadSignPos BSN.quadSignPos 7 8 9 101408700
  100000 24 100 137438953472 68719476736

noncomputable def p9803 :=
p9802 2305843009213693952 false 284540620532287 3360
  285796269294 43 48592008000 16 301984246446 43
  45812984488

noncomputable def p9804 :=
p9803 8 true 245311549434 142969 true 100334328721
  true 108817666162 7244019458077122842 1 false

noncomputable def p9805 :=
p9804 102413394056 false false 96564496015 false true
  176914781387 175257 BSN.abs_quadSignPos
  (BSN.cos_quad_nat0 24 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 102413394056 137438953472)

noncomputable def p9806 :=
BSN.mainSumRS_step2
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
      true 5))
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
    true 5)
  Real.sin Real.sin

noncomputable def p9807 :=
p9806 BSN.quadSignNeg BSN.quadSignNeg 5 6 7 101408700
  100000 161 61 137438953472 68719476736

noncomputable def p9808 :=
p9807 2305843009213693952 false 284540620532287 3360
  246257546308 43 56109217800 8 267443854420 43
  51947041624

noncomputable def p9809 :=
p9808 8 true 175361986709 106024 false 55979042597
  false 160079735458 7244019458077122842 1 false

noncomputable def p9810 :=
p9809 54444063682 true false 126262837393 true true
  245311549434 142969 BSN.abs_quadSignNeg
  (BSN.cos_quad_nat1 161 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 54444063682 137438953472)

noncomputable def p9811 :=
BSN.mainSumRS_step2
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
      true 5))
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
    true 5)
  Real.sin Real.cos

noncomputable def p9812 :=
p9811 BSN.quadSignPos BSN.quadSignNeg 3 4 5 101408700
  100000 423 278 137438953472 68719476736

noncomputable def p9813 :=
p9812 2305843009213693952 false 284540620532287 3360
  190530846192 42 68719476728 8 221199462352 42
  61464568544

noncomputable def p9814 :=
p9813 16 true 174319105731 62470 false 4887125775
  false 208089644420 7244019458077122842 1 false

noncomputable def p9815 :=
p9814 4886095953 false false 7794774106 true true
  175361986709 106024 BSN.abs_quadSignPos
  (BSN.cos_quad_nat3 423 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 4886095953 137438953472)

noncomputable def p9816 :=
p9797 BSN.quadSignNeg BSN.quadSignPos 1 2 3 101408700
  100000 870 608 137438953472 68719476736

noncomputable def p9817 :=
p9816 2305843009213693952 false 284540620532287 3360
  95265423088 42 97184016000 16 150992123216 42
  79350416784

noncomputable def p9818 :=
p9817 16 true 137437818376 3410 false 110108582299
  false 161200486953 7244019458077122842 1 false

noncomputable def p9819 :=
p9818 95641652372 true false 53256359689 false true
  174319105731 62470 BSN.abs_quadSignNeg
  (BSN.cos_quad_nat2 870 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 95641652372 137438953472)

noncomputable def p9820 :=
@Enclosure.Real.IsNear.recentre'
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
      true 5)
    1)

noncomputable def p9821 :=
@Enclosure.Real.IsNear.of_eq
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
      true 5)
    1)

noncomputable def p9822 :=
@p9821
  (Real.cos
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
        true 5)))
  true 17179727297

noncomputable def p9823 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
        true 5)))
  true 17179727297

noncomputable def p9824 :=
@Enclosure.Real.IsNear.cos_image
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
      true 5))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 35567577566535)
    (@Nat.cast.{0} Real Real.instNatCast 17179869184))
  false 35567577566535

noncomputable def p9825 :=
nat_lit 8112146872794273184407688067789498776814501433787248417821

noncomputable def p9826 :=
nat_lit 3918333257734246055798665948534605680012731069182771200

noncomputable def p9827 :=
@Enclosure.Real.IsNear.recentre'
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
      true 5))
  false p9825 p9826

noncomputable def p9828 :=
nat_lit 6291456000000000000000000

noncomputable def p9829 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 101408700 400000)
      (Real.log (Enclosure.sfrac false 41134907742760000 160000000000)))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 1 4)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 1 2) Real.pi)
        (Real.arctan
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@Nat.cast.{0} Real Real.instNatCast 100000)
            (@Nat.cast.{0} Real Real.instNatCast 202817400))))))

noncomputable def p9830 :=
nat_lit 514775159216144600985554102019360000000000000000

noncomputable def p9831 :=
nat_lit 3132161136641561549803824385734736345920000000000000

noncomputable def p9832 :=
@Enclosure.Real.IsNear.of_eq
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
      true 5))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (p9829 (Enclosure.sfrac false 101408700 200000))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 101408700 200000) (Real.log Real.pi)))
    (Enclosure.sfrac true p9830 p9831))
  false

noncomputable def p9833 :=
BSN.riemannSiegelThetaApproximant_two_zero_mk
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
    true 5)
  101408700 100000 41134907742760000 160000000000

noncomputable def p9834 :=
p9833 202817400 400000 200000 p9830
  p9831
  (Enclosure.sfrac_ofScientific_eq 101408700 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9835 :=
@Enclosure.Real.IsNear.addLit_ft_p
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (p9829 (Enclosure.sfrac false 101408700 200000))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 101408700 200000) (Real.log Real.pi)))
  (Enclosure.sfrac true p9830 p9831) 7459062235020028491869
  3602879701896396800

noncomputable def p9836 :=
nat_lit 23362982993647506771094141635233756477225764129307275443324480000000000000

noncomputable def p9837 :=
@p9835 153763639006470481 p9828 p9830
  p9831 0 1 p9836 p9825
  p9826 153763639006470481 p9828

noncomputable def p9838 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (p9829 (Enclosure.sfrac false 101408700 200000))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 101408700 200000) (Real.log Real.pi))
  47751369732649657440721 18014398509481984000 116197969937 12000000000000000000

noncomputable def p9839 :=
nat_lit 5125828537318350124410489106595840000

noncomputable def p9840 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 101408700 400000)
      (Real.log (Enclosure.sfrac false 41134907742760000 160000000000)))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 1 4)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 1 2) Real.pi)
        (Real.arctan
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@Nat.cast.{0} Real Real.instNatCast 100000)
            (@Nat.cast.{0} Real Real.instNatCast 202817400))))))

noncomputable def p9841 :=
@p9840 (Enclosure.sfrac false 101408700 200000)
  2275418136131687431801 720575940379279360 116197969937 12000000000000000000
  101408700 200000 0

noncomputable def p9842 :=
nat_lit 382010957861197259525768000

noncomputable def p9843 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 101408700 400000)
    (Real.log (Enclosure.sfrac false 41134907742760000 160000000000)))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 1 4)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 1 2) Real.pi)
      (Real.arctan
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@Nat.cast.{0} Real Real.instNatCast 100000)
          (@Nat.cast.{0} Real Real.instNatCast 202817400)))))
  2275701016821006027321

noncomputable def p9844 :=
nat_lit 5123786134997368029251908602479771648

noncomputable def p9845 :=
@p9843 720575940379279360 422725884269 44000000000000000000
  884002154120611 2251799813685248 20000033 264000000000000000
  p9844 2275418136131687431801 720575940379279360 116197969937

noncomputable def p9846 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 101408700 400000)
  (Real.log (Enclosure.sfrac false 41134907742760000 160000000000)) 101408700
  400000 0 1 56102213538409575 4503599627370496

noncomputable def p9847 :=
nat_lit 30842518064726728253217177600

noncomputable def p9848 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast 41134907742760000)
      (@Nat.cast.{0} Real Real.instNatCast 160000000000)))
  false p9847 p2333

noncomputable def p9849 :=
BSN.log_rat_reduce_isNear 41134907742760000 160000000000 17 82269815485520000
  41943040000000000 46295745987 68719476736 24973259072661432
  36028797018963968 26400000000 1000000000000000

noncomputable def p9850 :=
nat_lit
  889227448156213407581899684843490328012820890465233017066165345360739284702476737877417465112249681889851181965040733505049288807783529284192698121170743104844087465083838945015043974132580830204629423636104093389163625181275600340735850443718108837116629530179615617905596812636284388376576000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p9851 :=
nat_lit
  33380422263167380757969419420780051408542204454217520878640688067625716658093141369515354718481420870791756689016478645969183308921155608152140265765449355893808450048440299054482548570983289486573076801596478005345986582624592930064627417110291534228335969986539101543449715609224374491545600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p9852 :=
nat_lit
  689728163071162719121384882420552153371151089100818240106429687355284289092453051152006320605327519594177276883541671292986240165277762534927707575447890545194891576773657205377609670453859429547429089977488336947042137585784303466739592435813562222535287837559374315182056538112000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p9853 :=
BSN.log_dyadic_bound 20163387742760000 62106427742760000 12 11
  p9850 68719476736 26400000000 p9851 p9852
  46295745987 82269815485520000

noncomputable def p9854 :=
p9853 41943040000000000 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p9855 :=
@BSN.binarySplit_of_base11 (BSN.artanhP 20163387742760000) (BSN.artanhQ 62106427742760000)
  0 11 p9851 p9850 p9852
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p9856 :=
p9849 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p9854 (p9855 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

noncomputable def p9857 :=
@p9846 1250561 33000000000000000 2275701016821006027321
  720575940379279360 422725884269 44000000000000000000
  (Enclosure.Real.IsNear.const false 101408700 400000)
  (BSN.isNear_log_sfrac 41134907742760000 160000000000 56102213538409575
    4503599627370496 1250561 33000000000000000 false
    (@p9848 1000448800000000 p2422 56102213538409575
      4503599627370496 1250561 33000000000000000
      (p9856 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p9858 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 1 4)
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 1 2) Real.pi)
    (Real.arctan
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@Nat.cast.{0} Real Real.instNatCast 100000)
        (@Nat.cast.{0} Real Real.instNatCast 202817400))))
  1 4

noncomputable def p9859 :=
@p9858 0 1 884002154120611 562949953421312 20000033
  66000000000000000 884002154120611 2251799813685248 20000033
  264000000000000000 (Enclosure.Real.IsNear.const false 1 4)

noncomputable def p9860 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 1 2) Real.pi)
  (Real.arctan
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast 100000) (@Nat.cast.{0} Real Real.instNatCast 202817400)))
  884279719003555 562949953421312 1

noncomputable def p9861 :=
nat_lit 7593520683083151769075712

noncomputable def p9862 :=
@p9860 2000000000000000 4235304 8589934592 1
  3300000000 p9861 884002154120611 562949953421312 20000033
  66000000000000000
  (@p803 1 1000000000000000 884279719003555 562949953421312
    1 2000000000000000 (Enclosure.Real.IsNear.const false 1 2)
    BSN.pi_near_15 (Eq.refl true))

noncomputable def p9863 :=
BSN.arctan_dyadic_bound_f 100000 202817400 1 0 8589934592
  3300000000 0 1 1 0 1

noncomputable def p9864 :=
p9863 1 4235304 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)
  (@BSN.binarySplit_of_le (BSN.arctanEvenP 100000) (BSN.arctanEvenQ 202817400) 0
    0 (Eq.refl true))
  (@BSN.binarySplit_of_le (BSN.arctanOddP 100000) (BSN.arctanOddQ 202817400) 0 0
    (Eq.refl true))

noncomputable def p9865 :=
p9859
  (p9862
    (p9864 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p9866 :=
@p9838 79773395977398033 137438953472000 1014087
  68719476736000 p9839 7459062235020028491869 3602879701896396800
  153763639006470481 p9828
  (@p9841 1 p9842 47751369732649657440721
    18014398509481984000 116197969937 12000000000000000000
    (@p9845 12000000000000000000 p9857 p9865
      (Eq.refl true) (Eq.refl true))
    (Enclosure.Real.IsNear.const false 101408700 200000) (Eq.refl true)
    (Eq.refl true))

noncomputable def p9867 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 101408700 200000) (Real.log Real.pi)
  101408700 200000 0 1 78665238759 68719476736

noncomputable def p9868 :=
p9866
  (@p9867 1 34359738368 79773395977398033 137438953472000
    1014087 68719476736000
    (Enclosure.Real.IsNear.const false 101408700 200000) d91
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p9869 :=
@p9824 17179869184 421 17179869184 true 17179727297
  17179869184 1 3300000000
  (@p9827 153763639006470481 p9828 35567577566535
    17179869184 421 17179869184
    (@p9832 p9825 p9826 153763639006470481
      p9828
      (p9834 (Eq.refl true) (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (p9837 (p9868 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p9830 p9831)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p9870 :=
nat_lit 3879040838028543720192737280

noncomputable def p9871 :=
BSN.cos_reduce1
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 35567577566535)
    (@Nat.cast.{0} Real Real.instNatCast 17179869184))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast p9870)
    (@Nat.cast.{0} Real Real.instNatCast p2333))
  226375608064910080 72057594037927936 false

noncomputable def p9872 :=
BSN.sin_reduce_arg_pos_rat_q1 35567577566535 17179869184 226375608064910080
  72057594037927936 329 p9870 p2333
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p9873 :=
nat_lit
  1127562142796696876874647846084982355453718462701385412227153206037992017868380286063542523108913350171330464814505323870908824798225064075413867361998831696234917465704481

noncomputable def p9874 :=
nat_lit
  787289782743488969742431319565555636908056712177996918300683638413406918588570637167069411890634530473039944328641302392667379681271147571900676292680705880061134881

noncomputable def p9875 :=
nat_lit
  5630877151360253145219218694541915505195879962191238194396913638958845389062070835142793237968067620582432190220199880068541008559346211879317324430517454853091506127915041

noncomputable def p9876 :=
BSN.sin_dyadic_bound_f 55124485783559 35184372088832 4 3 17179869184
  6606445313 p9873 p3100 p9874 p9875
  p3103

noncomputable def p9877 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 55124485783559) (BSN.sinEvenQ 35184372088832) 0
  3 p9873 p3100 p9874 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9878 :=
p9876 p9874 17179727297 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p9877 (Eq.refl true))

noncomputable def p9879 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 55124485783559) (BSN.sinOddQ 35184372088832) 0
  3 p9875 p3103 p9874 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9880 :=
@BSN.sin_arg_round false 17179727297 17179869184 p9870
  p2333 55124485783559 35184372088832 6606445313 6600000000
  (p9878 (p9879 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p9881 :=
p9871 17179727297 17179869184 329 1000000000000000
  6600000000 3300000000 p9872 BSN.pi_near_15 p9880
  (Eq.refl true) (Eq.refl true)

noncomputable def p9882 :=
@p9822 17179869184 5494061989 221459251200000000
  (BSN.main_sum_rs_one
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
      true 5))
  (@p9823 17179869184 1406479869184 56693568307200000000
    17179727297 17179869184 5494061989 221459251200000000
    (p9869 (Enclosure.sfrac_false_div 35567577566535 17179869184)
      (p9881 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p9883 :=
@p9820 true 17179727297 17179869184 5494061989
  221459251200000000 137437818376 137438953472 3410 137438953472
  p9882 (Eq.refl true)

noncomputable def p9884 :=
p9819 BSN.abs_quadSignPos (BSN.cos_quad_nat0 608 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 53256359689 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101408700 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true) p9883
  (@p9827 153763639006470481 p9828 284540620532287
    137438953472 3360 137438953472
    (@p9832 p9825 p9826 153763639006470481
      p9828
      (p9834 (Eq.refl true) (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (p9837 (p9868 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p9830 p9831)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p9885 :=
nat_lit
  373590312474291341926681256224853991071899609786193333902930735446049660668056069289172463017503558204759321297751981977527026524058526416081

noncomputable def p9886 :=
nat_lit
  3175806630306452577483858550065395883505303031566552261584269763413853299772829266168972952520613306367271853192442958662607094152401

noncomputable def p9887 :=
nat_lit
  2266077468445735053171422149970672125913461022149318437340695215028413873442029563895441637233971380716451086736994906477836750526240208977105

noncomputable def p9888 :=
BSN.cos_dyadic_bound_f 110108582299 137438953472 4 3 137438953472
  68719476736 p9885 p2457 p9886 p9887
  p2460

noncomputable def p9889 :=
@BSN.binarySplit_of_base3 (BSN.cosEvenP 110108582299) (BSN.cosEvenQ 137438953472) 0
  3 p9885 p2457 p9886 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9890 :=
p9888 p9886 95641652372 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p9889 (Eq.refl true))

noncomputable def p9891 :=
@BSN.binarySplit_of_base3 (BSN.cosOddP 110108582299) (BSN.cosOddQ 137438953472) 0
  3 p9887 p2460 p9886 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9892 :=
nat_lit
  1717745642132158468152561098751387842243853430115119459894443496709233070781286447444990279557161885234962068538171057888063660253865055706721

noncomputable def p9893 :=
nat_lit
  307890431734662303905567733739965977127435777765088062135813828716487072563336278570581078280225749689374971584065930281374022395846241

noncomputable def p9894 :=
nat_lit
  10413171572547723384240227394190602387493917195255997994712511420022800851753252335440937227952332246665654589175429628139282727485028192050785

noncomputable def p9895 :=
BSN.cos_dyadic_bound_f 161200486953 137438953472 4 3 137438953472
  68719476736 p9892 p2457 p9893 p9894
  p2460

noncomputable def p9896 :=
@BSN.binarySplit_of_base3 (BSN.cosEvenP 161200486953) (BSN.cosEvenQ 137438953472) 0
  3 p9892 p2457 p9893 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9897 :=
p9895 p9893 53256359689 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p9896 (Eq.refl true))

noncomputable def p9898 :=
@BSN.binarySplit_of_base3 (BSN.cosOddP 161200486953) (BSN.cosOddQ 137438953472) 0
  3 p9894 p2460 p9893 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9899 :=
p9884 d93 d95 d97 d99 d103
  (p9890 (p9891 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p9897 (p9898 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p9900 :=
p9815 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 278 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 7794774106 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101408700 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p9899 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p9827 153763639006470481 p9828 284540620532287
    137438953472 3360 137438953472
    (@p9832 p9825 p9826 153763639006470481
      p9828
      (p9834 (Eq.refl true) (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (p9837 (p9868 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p9830 p9831)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p9901 :=
nat_lit 570445376737096294033203955259187890625

noncomputable def p9902 :=
BSN.sin_dyadic_bound_f 4887125775 137438953472 2 1 137438953472
  68719476736 p9901 p3178 p9901 p9901
  p3179

noncomputable def p9903 :=
@BSN.binarySplit_of_base (BSN.sinEvenP 4887125775) (BSN.sinEvenQ 137438953472) 0
  1 p9901 p3178 p9901 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9904 :=
p9902 p9901 4886095953 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p9903 (Eq.refl true))

noncomputable def p9905 :=
@BSN.binarySplit_of_base (BSN.sinOddP 4887125775) (BSN.sinOddQ 137438953472) 0 1
  p9901 p3179 p9901 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9906 :=
nat_lit
  74487810549875741380148230273671511988284032081067370401201636268336610705141303276213625509193859209554519641852338640857258911713970477419151911868335807948365270181292686453317304320000000

noncomputable def p9907 :=
nat_lit
  12359687474908976227581512811856756772743635659056009304224844368964039890735240514395177806904949953629236673139845301487798882901916894769758083602779460602115522560000000000000000

noncomputable def p9908 :=
nat_lit
  758195398453616232217039597894462011352350863506800033114449559563353907203937475681059335565025811188179535573571695420537248857370677245176050469320461744634482211392001783830427992064000000

noncomputable def p9909 :=
BSN.cos_dyadic_bound_f 208089644420 137438953472 5 4 137438953472
  68719476736 p9906 p2495 p9907 p9908
  p2498

noncomputable def p9910 :=
@BSN.binarySplit_of_base4 (BSN.cosEvenP 208089644420) (BSN.cosEvenQ 137438953472) 0
  4 p9906 p2495 p9907 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9911 :=
p9909 p9907 7794774106 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p9910 (Eq.refl true))

noncomputable def p9912 :=
@BSN.binarySplit_of_base4 (BSN.cosOddP 208089644420) (BSN.cosOddQ 137438953472) 0
  4 p9908 p2498 p9907 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9913 :=
p9900 d105 d107 d109 d111 d103
  (p9904 (p9905 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p9911 (p9912 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p9914 :=
p9810 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 61 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 126262837393 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101408700 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p9913 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p9827 153763639006470481 p9828 284540620532287
    137438953472 3360 137438953472
    (@p9832 p9825 p9826 153763639006470481
      p9828
      (p9834 (Eq.refl true) (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (p9837 (p9868 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p9830 p9831)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p9915 :=
nat_lit 10595634372987927908153826589395696089741221126000634399303204462235700658658416137577229025

noncomputable def p9916 :=
nat_lit 96428127189048381315985601990250814967240965997999739084630403002970259511571343796961

noncomputable def p9917 :=
nat_lit 27750314855143409871595034233633124590859917892247188570026065142345782630351880673383738081

noncomputable def p9918 :=
BSN.sin_dyadic_bound_f 55979042597 137438953472 3 2 137438953472
  68719476736 p9915 p2477 p9916 p9917
  p2480

noncomputable def p9919 :=
@BSN.binarySplit_of_base2 (BSN.sinEvenP 55979042597) (BSN.sinEvenQ 137438953472) 0
  2 p9915 p2477 p9916 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9920 :=
p9918 p9916 54444063682 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p9919 (Eq.refl true))

noncomputable def p9921 :=
@BSN.binarySplit_of_base2 (BSN.sinOddP 55979042597) (BSN.sinOddQ 137438953472) 0
  2 p9917 p2480 p9916 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9922 :=
nat_lit
  4340976886941603712954174325509152953597420700607064224571849697787689743862374727643356503411680504427296043751825814764024358097188745383936

noncomputable def p9923 :=
nat_lit
  283162863269394960539482368759054572856236249644605934106280814331853689626223200914390357098328243056629014574703640401377839057473536

noncomputable def p9924 :=
nat_lit
  21696722483217813472939268041515547219440838040088891661630946107231868714257340935693110415805500251156683465066454787319420425758946040221696

noncomputable def p9925 :=
BSN.sin_dyadic_bound_f 160079735458 137438953472 4 3 137438953472
  68719476736 p9922 p2504 p9923 p9924
  p2507

noncomputable def p9926 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 160079735458) (BSN.sinEvenQ 137438953472) 0
  3 p9922 p2504 p9923 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9927 :=
p9925 p9923 126262837393 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p9926 (Eq.refl true))

noncomputable def p9928 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 160079735458) (BSN.sinOddQ 137438953472) 0
  3 p9924 p2507 p9923 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9929 :=
p9914 d113 d115 d117 d119 d103
  (p9920 (p9921 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p9927 (p9928 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p9930 :=
p9805 BSN.abs_quadSignPos (BSN.cos_quad_nat0 100 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 96564496015 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101408700 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p9929 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p9827 153763639006470481 p9828 284540620532287
    137438953472 3360 137438953472
    (@p9832 p9825 p9826 153763639006470481
      p9828
      (p9834 (Eq.refl true) (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (p9837 (p9868 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p9830 p9831)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p9931 :=
nat_lit
  257558599775320732869620620946502964883218013135606916667228573571929612559266619919621076489673382696771263448911680200303341689717442915521

noncomputable def p9932 :=
nat_lit
  1040865449636213900030018177688012248748378346233970321441636412442548775528738371504537821631037425418853942231184187868754287439041

noncomputable def p9933 :=
nat_lit
  1562346086275383512945543063668431300055623826022830634319453932660305658867869893362964774712544925052162190507088939637878877357519785864385

noncomputable def p9934 :=
BSN.cos_dyadic_bound_f 100334328721 137438953472 4 3 137438953472
  68719476736 p9931 p2457 p9932 p9933
  p2460

noncomputable def p9935 :=
@BSN.binarySplit_of_base3 (BSN.cosEvenP 100334328721) (BSN.cosEvenQ 137438953472) 0
  3 p9931 p2457 p9932 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9936 :=
p9934 p9932 102413394056 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p9935 (Eq.refl true))

noncomputable def p9937 :=
@BSN.binarySplit_of_base3 (BSN.cosOddP 100334328721) (BSN.cosOddQ 137438953472) 0
  3 p9933 p2460 p9932 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9938 :=
nat_lit
  356372058185000785037667555529144754932078198887757707293417530958006021301394578164362744953490876853795191227121904272403094103466750119936

noncomputable def p9939 :=
nat_lit
  2756721459862061487599286343917890303540229191797761945833406350805500487002813214755777199291271033524116425553703488821814638022656

noncomputable def p9940 :=
nat_lit
  2161653410248031719159153926662820165972592978649027077149286714506280357314891179283096407206030359266017973126197953568664506738616405463040

noncomputable def p9941 :=
BSN.cos_dyadic_bound_f 108817666162 137438953472 4 3 137438953472
  68719476736 p9938 p2457 p9939 p9940
  p2460

noncomputable def p9942 :=
@BSN.binarySplit_of_base3 (BSN.cosEvenP 108817666162) (BSN.cosEvenQ 137438953472) 0
  3 p9938 p2457 p9939 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9943 :=
p9941 p9939 96564496015 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p9942 (Eq.refl true))

noncomputable def p9944 :=
@BSN.binarySplit_of_base3 (BSN.cosOddP 108817666162) (BSN.cosOddQ 137438953472) 0
  3 p9940 p2460 p9939 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9945 :=
p9930 d121 d123 d125 d127 d103
  (p9936 (p9937 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p9943 (p9944 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p9946 :=
p9801 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 230 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 136933685080 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101408700 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p9945 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p9827 153763639006470481 p9828 284540620532287
    137438953472 3360 137438953472
    (@p9832 p9825 p9826 153763639006470481
      p9828
      (p9834 (Eq.refl true) (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (p9837 (p9868 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p9830 p9831)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p9947 :=
nat_lit
  414715440424411776865154543792397243516823928326609946002259795415774090039024445020672034741852639818712153503673438775486274458973766680576

noncomputable def p9948 :=
nat_lit
  4343928773955517738808311090714671404374632139498862487732248131958037929842147119899623067096361833730309780870091361098925390954496

noncomputable def p9949 :=
nat_lit
  2515483891166871390386660715671287195856383972674123732421381266628245839627629866867204158765647918279111623564119573976970691870269447864320

noncomputable def p9950 :=
BSN.cos_dyadic_bound_f 113020413348 137438953472 4 3 137438953472
  68719476736 p9947 p2457 p9948 p9949
  p2460

noncomputable def p9951 :=
@BSN.binarySplit_of_base3 (BSN.cosEvenP 113020413348) (BSN.cosEvenQ 137438953472) 0
  3 p9947 p2457 p9948 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9952 :=
p9950 p9948 93529202680 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p9951 (Eq.refl true))

noncomputable def p9953 :=
@BSN.binarySplit_of_base3 (BSN.cosOddP 113020413348) (BSN.cosOddQ 137438953472) 0
  3 p9949 p2460 p9948 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9954 :=
nat_lit 19313300217406404570114913381309207210000

noncomputable def p9955 :=
BSN.cos_dyadic_bound_f 11788651330 137438953472 2 1 137438953472
  68719476736 p9954 p2486 p9954 p9954
  p2487

noncomputable def p9956 :=
@BSN.binarySplit_of_base (BSN.cosEvenP 11788651330) (BSN.cosEvenQ 137438953472) 0
  1 p9954 p2486 p9954 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9957 :=
p9955 p9954 136933685080 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p9956 (Eq.refl true))

noncomputable def p9958 :=
@BSN.binarySplit_of_base (BSN.cosOddP 11788651330) (BSN.cosOddQ 137438953472) 0
  1 p9954 p2487 p9954 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9959 :=
p9946 d129 d131 d133 d135 d103
  (p9952 (p9953 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p9957 (p9958 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p9960 :=
p9796
  (p9959 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p9827 153763639006470481 p9828 284540620532287
    137438953472 3360 137438953472
    (@p9832 p9825 p9826 153763639006470481
      p9828
      (p9834 (Eq.refl true) (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (p9837 (p9868 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p9830 p9831)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p9961 :=
nat_lit 3524601510282935226476365411312535706138353882138780094166313259878590338141076349006807296

noncomputable def p9962 :=
nat_lit 34571183423198156413755032862476528220076196823496944028070295472108285639601771151616

noncomputable def p9963 :=
nat_lit 10573735388481959283116268723871882165358621494022693288610883639044826797851949843478118656

noncomputable def p9964 :=
BSN.cos_dyadic_bound_f 49242407842 137438953472 3 2 137438953472
  68719476736 p9961 p2466 p9962 p9963
  p2469

noncomputable def p9965 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP 49242407842) (BSN.cosEvenQ 137438953472) 0
  2 p9961 p2466 p9962 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9966 :=
p9964 p9962 128711492185 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p9965 (Eq.refl true))

noncomputable def p9967 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP 49242407842) (BSN.cosOddQ 137438953472) 0
  2 p9963 p2469 p9962 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9968 :=
p9960 d137 d139 d103
  (p9966 (p9967 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true) (Eq.refl true)

noncomputable def p9969 :=
@p9785 p9769 p9771 p9772
  (p9789
    (@p9792 217857 68719476736
      (p9968 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (p9968 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true) (Eq.refl true)))

noncomputable def p9970 :=
@Enclosure.Real.IsNear.mulLit_ff p9776
  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
        (Enclosure.sfrac false 12 1)))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Zeta.RiemannSiegel.correctionLinear
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
          (Enclosure.sfrac false 12 1)))
      (@Inv.inv.{0} Real Real.instInv p9777)))

noncomputable def p9971 :=
nat_lit
  211214374469885475433349633257307412166844871636026901534269047770862812792607430311093623383541833950774356537273816090870077257092617907630166070415426244890743381

noncomputable def p9972 :=
nat_lit
  460688772561223309599799143187044542348256984914116263229517370635452168260760357920669766257038423772151901248872539660616526444082616288154471954520592778765795328

noncomputable def p9973 :=
nat_lit
  2107525485998888379449169502246897839831249975321063228468640474707353090547254157643893912059564760356856175089483931492394010766867458755130715938527901683501728535053163575154385419983643976671953394088869393558651

noncomputable def p9974 :=
nat_lit
  13390289216360285818259169445723168324940984005886086704998706165783711219158258333256270016099390414966120927309135068109058733961072202686346035200000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p9975 :=
@p9970 1204997163 4294967296 1 8589934592
  p9971 p9972 p9973 p9974
  p9782 p9769 p9783

noncomputable def p9976 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HPow.hPow.{0, 0, 0} Real Nat Real
    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
    (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)))
    12)
  (p9775
    (@Neg.neg.{0} Real Real.instNeg
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
        (@OfNat.ofNat.{0} Real 4
          (@instOfNatAtLeastTwo.{0} Real 4 Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))))))

noncomputable def p9977 :=
@p9976 1 1 0 1 1204997163 4294967296
  1 8589934592 1204997163 4294967296 1

noncomputable def p9978 :=
@Enclosure.Real.IsNear.of_eq
  (p9775
    (@Neg.neg.{0} Real Real.instNeg
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
        (@OfNat.ofNat.{0} Real 4
          (@instOfNatAtLeastTwo.{0} Real 4 Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))))))

noncomputable def p9979 :=
BSN.rpow_neg_quarter_mk
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p9980 :=
p9979
  (BSN.t_div_two_pi_nonneg
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
      true 5)
    101408700 100000
    (Enclosure.sfrac_ofScientific_eq 101408700 5 100000 (Eq.refl true)))

noncomputable def p9981 :=
@Enclosure.Real.IsNear.recentre' (@Inv.inv.{0} Real Real.instInv (Real.sqrt p9777)) false
  4819988652 17179869184 2 17179869184 1204997163 4294967296

noncomputable def p9982 :=
@Enclosure.Real.IsNear.recentre' (Real.sqrt p9777) false 61234149385
  17179869184 7 17179869184 61234149385 17179869184 7
  17179869184

noncomputable def p9983 :=
@Enclosure.Real.IsNear.sqrt_image
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p9984 :=
@Enclosure.Real.IsNear.of_eq
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p9985 :=
@p9984
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 101408700 100000)
    (@Inv.inv.{0} Real Real.instInv
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)))
  false 2772778639157961

noncomputable def p9986 :=
@p9985 17179869184000 1014087 17179869184000
  (BSN.t_div_two_pi_mk
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
      true 5)
    101408700 100000
    (Enclosure.sfrac_ofScientific_eq 101408700 5 100000 (Eq.refl true)))

noncomputable def p9987 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 101408700 100000)
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi))
  101408700 100000 0

noncomputable def p9988 :=
@p9987 1 2734261103 17179869184 1 17179869184
  2772778639157961 17179869184000 1014087 17179869184000
  (Enclosure.Real.IsNear.const false 101408700 100000) d142

noncomputable def p9989 :=
@p9983 2772778639157961 17179869184000 1014087 17179869184000
  109128335320 109128335361 8589934592
  (p9986 (p9988 (Eq.refl true))) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p9990 :=
@Enclosure.Real.IsNear.recentre' p9777 false 218256670681 17179869184
  41 17179869184 218256670681 17179869184 41 17179869184
  (p9989 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p9991 :=
@Enclosure.Real.IsNear.sqrt_image p9777 218256670681 17179869184 41
  17179869184 30617074689 30617074696 8589934592
  (p9990 (Eq.refl true)) (Eq.refl true) (Eq.refl true)

noncomputable def p9992 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt p9777) 61234149385 17179869184
  7 17179869184 2409994325 2409994327 8589934592
  (p9982
    (p9991 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p9993 :=
@p9978 (@Inv.inv.{0} Real Real.instInv (Real.sqrt p9777)) false
  1204997163 4294967296 1 8589934592 p9980
  (@p9981 1 8589934592
    (p9992 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p9994 :=
@Enclosure.Real.IsNear.addLit_ft_p
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
      (Enclosure.sfrac false 12 1)))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Zeta.RiemannSiegel.correctionLinear
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
        (Enclosure.sfrac false 12 1)))
    (@Inv.inv.{0} Real Real.instInv p9777))
  4235629233237375341

noncomputable def p9995 :=
nat_lit 21617278211378380800000000

noncomputable def p9996 :=
nat_lit
  346736226671551915263287037433568502054111614181739682815151582976868674602746129611117555020911174736578118459519065797026069744691923608198595315788602676456875

noncomputable def p9997 :=
nat_lit
  51371307179263384191314467045428948010246796813932999530798844760252328673512095126186577027361012812248228261504771029063647261944261596593680162527901683501728535053163575154385419983643976671953394088869393558651

noncomputable def p9998 :=
nat_lit
  1948108755267314955833232918127310360949221770537043949718243807578815468101368299919113459164644197189042265648860089842366213748544506381722670966735493898159301239708384761214926848

noncomputable def p9999 :=
@p9994 9223372036854775808 3319454584649662429 p9995
  p9996 p9972 p9997 p9974
  p9998 p9971 p9972 p9973

noncomputable def p10000 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (@Inv.inv.{0} Real Real.instInv
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
          (Enclosure.sfrac false 12 1)))))

noncomputable def p10001 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
        (Enclosure.sfrac false 12 1))
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
        (Enclosure.sfrac false 12 1)))
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
      (Enclosure.sfrac false 12 1)))

noncomputable def p10002 :=
@Enclosure.Real.IsNear.of_eq
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
      (Enclosure.sfrac false 12 1)))
  (p10000
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p10001 (Enclosure.sfrac false 1 16)))))

noncomputable def p10003 :=
BSN.cos_two_pi_p_ne_zero_mk
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
    true 5)
  101408700 100000 12
  (Enclosure.sfrac_ofScientific_eq 101408700 5 100000 (Eq.refl true))

noncomputable def p10004 :=
@Enclosure.Real.IsNear.mulLit_tt
  (@Inv.inv.{0} Real Real.instInv
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
          (Enclosure.sfrac false 12 1)))))

noncomputable def p10005 :=
@p10004
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p10001 (Enclosure.sfrac false 1 16))))
  3784077569

noncomputable def p10006 :=
@p10005 1073741824 1641 8589934592 1119329389
  8589934592 4042538807 110729625600000000 4235629233237375341
  9223372036854775808 3319454584649662429 p9995

noncomputable def p10007 :=
@Enclosure.Real.IsNear.of_eq
  (@Inv.inv.{0} Real Real.instInv
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
          (Enclosure.sfrac false 12 1)))))

noncomputable def p10008 :=
@Inv.inv.{0} Real Real.instInv
  (@Neg.neg.{0} Real Real.instNeg
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
          (Enclosure.sfrac false 12 1)))))

noncomputable def p10009 :=
@p10007 (@Neg.neg.{0} Real Real.instNeg p10008) true 3784077569
  1073741824 1641 8589934592
  (BSN.inv_eq_neg_inv_neg
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
          (Enclosure.sfrac false 12 1)))))

noncomputable def p10010 :=
@Enclosure.Real.IsNear.inv_image
  (@Neg.neg.{0} Real Real.instNeg
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
          (Enclosure.sfrac false 12 1)))))

noncomputable def p10011 :=
@Enclosure.Real.IsNear.neg
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
        (Enclosure.sfrac false 12 1))))
  true

noncomputable def p10012 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
        (Enclosure.sfrac false 12 1))))
  true

noncomputable def p10013 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
      (Enclosure.sfrac false 12 1)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 38007743391)
    (@Nat.cast.{0} Real Real.instNatCast 8589934592))
  false

noncomputable def p10014 :=
nat_lit 10698228685901876331881515

noncomputable def p10015 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
      (Enclosure.sfrac false 12 1)))
  false p10014

noncomputable def p10016 :=
nat_lit 1106429195693900205019069663

noncomputable def p10017 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
    (Enclosure.sfrac false 12 1))
  884279719003555 140737488355328 1

noncomputable def p10018 :=
@Enclosure.Real.IsNear.subLit_ff_p p9777 (Enclosure.sfrac false 12 1)
  218256670681 17179869184 41 17179869184 12 1 0

noncomputable def p10019 :=
@p10017 500000000000000 12098240473 17179869184 41
  17179869184 p10014 p2602 p10016
  p5018 d141
  (@p10018 1 12098240473 12098240473 17179869184 41
    17179869184 (p9990 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p10020 :=
@p10013 38007743391 8589934592 259 17179869184 true
  4874832436 17179869184 1 3300000000
  (@p10015 p2602 p10016 p5018
    38007743391 8589934592 259 17179869184
    (p10019 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div 38007743391 8589934592)

noncomputable def p10021 :=
nat_lit 1588389754129222470553567232

noncomputable def p10022 :=
BSN.cos_reduce2
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 38007743391)
    (@Nat.cast.{0} Real Real.instNatCast 8589934592))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast p10021)
    (@Nat.cast.{0} Real Real.instNatCast p2445))
  226375608064910080 72057594037927936 false

noncomputable def p10023 :=
BSN.sin_reduce_arg_pos_rat_q2 38007743391 8589934592 226375608064910080
  72057594037927936 0 p10021 p2445 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p10024 :=
nat_lit
  195008481691881352567059629827513554937260993965004556445875540680514061724987144709817300686880999942641711094368469068313146582425131878830914316384323777693619372444561

noncomputable def p10025 :=
nat_lit
  71661726211239619502236894811403232143704986263594570533933288522662235636927822752730201432680424143692205217770145487492354042934501270379180118892847893228833681

noncomputable def p10026 :=
nat_lit
  1181780715251048622273933020146361139263519414344190395447950017341814952206946888378778653275218160511122960209180886505204465720139726191975734977671684169369082534316945

noncomputable def p10027 :=
BSN.cos_dyadic_bound_f 45144752054091 35184372088832 4 3 17179869184
  6606445313 p10024 p2613 p10025
  p10026 p2616

noncomputable def p10028 :=
@BSN.binarySplit_of_base3 (BSN.cosEvenP 45144752054091) (BSN.cosEvenQ 35184372088832) 0
  3 p10024 p2613 p10025 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p10029 :=
p10027 p10025 4874832436 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p10028 (Eq.refl true))

noncomputable def p10030 :=
@BSN.binarySplit_of_base3 (BSN.cosOddP 45144752054091) (BSN.cosOddQ 35184372088832) 0
  3 p10026 p2616 p10025 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p10031 :=
@BSN.cos_arg_round false 4874832436 17179869184 p10021
  p2445 45144752054091 35184372088832 6606445313 6600000000
  (p10029 (p10030 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p10032 :=
p10022 4874832436 17179869184 0 1000000000000000
  6600000000 3300000000 p10023 BSN.pi_near_15 p10031
  (Eq.refl true) (Eq.refl true)

noncomputable def p10033 :=
@p10011 1218708109 4294967296 3405780739 221459251200000000
  (@p10012 4874832436 17179869184 871879869184
    56693568307200000000 1218708109 4294967296 3405780739
    221459251200000000
    (p10020 (p10032 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p10034 :=
@p10010 1218708109 4294967296 3405780739 221459251200000000
  30272618911 30272622193 8589934592 p10033
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p10035 :=
@Enclosure.Real.IsNear.recentre' p10008 false 60545241104 17179869184
  3282 17179869184 3784077569 1073741824 1641 8589934592
  (p10034 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p10036 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p10001 (Enclosure.sfrac false 1 16))))
  true

noncomputable def p10037 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p10001 (Enclosure.sfrac false 1 16)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Neg.neg.{0} Real Real.instNeg (@Nat.cast.{0} Real Real.instNatCast 29231118471))
    (@Nat.cast.{0} Real Real.instNatCast 17179869184))
  true

noncomputable def p10038 :=
nat_lit 70676507713153151462654984634172045

noncomputable def p10039 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p10001 (Enclosure.sfrac false 1 16)))
  true p10038

noncomputable def p10040 :=
nat_lit 9155999645409052571853353088727199937

noncomputable def p10041 :=
nat_lit 253530120045645880299340641075200000000000000

noncomputable def p10042 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (p10001 (Enclosure.sfrac false 1 16)) 884279719003555
  140737488355328 1

noncomputable def p10043 :=
@Enclosure.Real.IsNear.subLit_tf
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
        (Enclosure.sfrac false 12 1))
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
        (Enclosure.sfrac false 12 1)))
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
      (Enclosure.sfrac false 12 1)))

noncomputable def p10044 :=
@p10043 (Enclosure.sfrac false 1 16) 61478766140179020303
  295147905179352825856 1696430357011 295147905179352825856 1 16
  0

noncomputable def p10045 :=
@Enclosure.Real.IsNear.subLit_ff_n
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
      (Enclosure.sfrac false 12 1))
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
      (Enclosure.sfrac false 12 1)))
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
    (Enclosure.sfrac false 12 1))
  146367422542535263729

noncomputable def p10046 :=
nat_lit 1056197159882004175146820042752

noncomputable def p10047 :=
@p10045 295147905179352825856 992055720467 295147905179352825856
  12098240473 17179869184 41 17179869184 p10046
  61478766140179020303 295147905179352825856 1696430357011

noncomputable def p10048 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
    (Enclosure.sfrac false 12 1))
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
    (Enclosure.sfrac false 12 1))
  12098240473 17179869184 41

noncomputable def p10049 :=
@p10048 17179869184 12098240473 17179869184 41
  17179869184 146367422542535263729 295147905179352825856 992055720467
  295147905179352825856
  (@p10018 1 12098240473 12098240473 17179869184 41
    17179869184 (p9990 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p10050 :=
p10049
  (@p10018 1 12098240473 12098240473 17179869184 41
    17179869184 (p9990 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p10051 :=
@p10047 295147905179352825856 (p10050 (Eq.refl true))
  (@p10018 1 12098240473 12098240473 17179869184 41
    17179869184 (p9990 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p10052 :=
@p10042 500000000000000 79925510213888571919 295147905179352825856
  1696430357011 295147905179352825856 p10038 p2630
  p10040 p10041 d141
  (@p10044 1 1278808163422217150704 79925510213888571919
    295147905179352825856 1696430357011 295147905179352825856
    (p10051 (Eq.refl true) (Eq.refl true))
    (Enclosure.Real.IsNear.const false 1 16) (Eq.refl true)
    (Eq.refl true))

noncomputable def p10053 :=
@p10037 29231118471 17179869184 311 8589934592 true
  1119329389 8589934592 1 3300000000
  (@p10039 p2630 p10040 p10041
    29231118471 17179869184 311 8589934592
    (p10052 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_true_div 29231118471 17179869184)

noncomputable def p10054 :=
nat_lit
  422854584248873613621287319973340672973142764000814447463063786129350355155742898557734687508190228554979364833529633611718322046617302225485984961084490421613733085605763593601

noncomputable def p10055 :=
nat_lit
  284136436553030447218947253302026913422337203343204242227217077318223340306546516109506827700691510517424804602570863391611145348644459833029198104374091865892475483521

noncomputable def p10056 :=
nat_lit
  4298830648879824744506739382841222265724658989345964642408256903092670311219891574216625984435050685816361644290978086290635117524681568008452265947883027473218893981701997966721

noncomputable def p10057 :=
BSN.cos_dyadic_bound_t 29231118471 17179869184 5 4 8589934592
  3300000000 p10054 p3287 p10055
  p10056 p3290

noncomputable def p10058 :=
@BSN.binarySplit_of_base4 (BSN.cosEvenP 29231118471) (BSN.cosEvenQ 17179869184) 0
  4 p10054 p3287 p10055 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p10059 :=
p10057 p10055 1119329389 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p10058 (Eq.refl true))

noncomputable def p10060 :=
@BSN.binarySplit_of_base4 (BSN.cosOddP 29231118471) (BSN.cosOddQ 17179869184) 0
  4 p10056 p3290 p10055 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p10061 :=
p10053
  (BSN.cos_neg_of_bound 29231118471 17179869184 true 1119329389 8589934592
    1 3300000000
    (p10059 (p10060 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p10062 :=
p10006
  (p10009
    (@Enclosure.Real.IsNear.neg p10008 false 3784077569 1073741824
      1641 8589934592 (p10035 (Eq.refl true))))
  (@p10036 1119329389 8589934592 1034889934592
    28346784153600000000 1119329389 8589934592 4042538807
    110729625600000000 (p10061 (Eq.refl true)) (Eq.refl true))

noncomputable def p10063 :=
@p9999 p9974
  (@p10002 false 4235629233237375341 9223372036854775808
    3319454584649662429 p9995
    (BSN.correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
        (Enclosure.sfrac false 12 1))
      (p10003 (Eq.refl true) (Eq.refl true)
        (p9780 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p10062 (Eq.refl true)))

noncomputable def p10064 :=
nat_lit
  512810649270665353062944215924118387024017241258695712239074528499158077295902848432554143705786598633211667817652330223513809301007036708894864232108125

noncomputable def p10065 :=
@Enclosure.Real.IsNear.mulLit_tf
  (Zeta.RiemannSiegel.correctionLinear
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
      (Enclosure.sfrac false 12 1)))
  (@Inv.inv.{0} Real Real.instInv p9777) p10064 p7279

noncomputable def p10066 :=
nat_lit
  75954306908315062198678874015819478565391932784880218264891623625243480683140448905566453985451212616349615709821708653523610439387446181123900945833840023115561789018711647224751516046676754250330757726637

noncomputable def p10067 :=
nat_lit
  1558834828478317453788962383489493318477294408470169490319526075127500949795155126282045386743195170416277941235938932293683608756525465600000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p10068 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
      (Enclosure.sfrac false 12 1)))
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 96 1)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi)))

noncomputable def p10069 :=
@Enclosure.Real.IsNear.of_eq
  (Zeta.RiemannSiegel.correctionLinear
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
      (Enclosure.sfrac false 12 1)))
  (@Neg.neg.{0} Real Real.instNeg p10068) true p10064

noncomputable def p10070 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
      (Enclosure.sfrac false 12 1)))
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 96 1)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi)))

noncomputable def p10071 :=
nat_lit
  110476064744507297515416186706721218711654142769399827692387144970703317374674656643175686183258170930141131936820065753267350748491418071208875

noncomputable def p10072 :=
nat_lit
  147260989444846946456569897885736783436831331053192811469499958238371633241160142802425245241910316818804940584867004123026926452861500498172115494027410973630151189001782041905545151769489539417263

noncomputable def p10073 :=
nat_lit
  3189942039240317418284726375396858171892665649518568309957967057050043092239410756642066298965973267910726797509471541762457600000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p10074 :=
@p10070 p10071 p7287 p10072
  p10073 4641825815 4398046511104 1 4398046511104
  p10064 p7279 p10066

noncomputable def p10075 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p10076 :=
p10075
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p10077 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p10076
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p10078 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p10077
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p10001 (Enclosure.sfrac false 1 16)))))

noncomputable def p10079 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (Enclosure.sfrac false 3 1)
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p10080 :=
p10078
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p10079
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 4 1) Real.pi))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p10001 (Enclosure.sfrac false 1 16)))))

noncomputable def p10081 :=
@Neg.neg.{0} Real Real.instNeg
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
          (Enclosure.sfrac false 12 1)))))

noncomputable def p10082 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p10080
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 3 1) p10081)
    (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
        (Enclosure.sfrac false 12 1))))

noncomputable def p10083 :=
@Neg.neg.{0} Real Real.instNeg
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 4 1)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
          (Enclosure.sfrac false 12 1)))))

noncomputable def p10084 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p10082
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 3 1) p10083)
    (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
        (Enclosure.sfrac false 12 1))))

noncomputable def p10085 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 8 1)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi) Real.pi))
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
        (Enclosure.sfrac false 12 1))))

noncomputable def p10086 :=
@Enclosure.Real.IsNear.of_eq
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
      (Enclosure.sfrac false 12 1)))
  (p10000
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p10084
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p10085
        (Zeta.RiemannSiegel.correction
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
            (Enclosure.sfrac false 12 1))))))

noncomputable def p10087 :=
@p10004
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p10084
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p10085
      (Zeta.RiemannSiegel.correction
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
          (Enclosure.sfrac false 12 1)))))
  15499581200943

noncomputable def p10088 :=
nat_lit
  7127680632931288148518618166448791647395797522961819808927105004029725484187574404370797032886056903791025029537258022843463437125

noncomputable def p10089 :=
nat_lit
  9500570770300676413373683887544894997077478042283074055829718652496126925068189217575287145418041687148655531742925092959174702637921786068899849992653115069825988903266689494679157963

noncomputable def p10090 :=
nat_lit
  725308845912949759232271020527345665844374172938516564945068025065221057102328531218987859339443563819878999654400000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p10091 :=
@p10087 4398046511104 3283 4398046511104 p10088
  p7305 p10089 p10090 p10071
  p7287 p10072 p10073

noncomputable def p10092 :=
@p10007 (@Neg.neg.{0} Real Real.instNeg p10008) true 15499581200943
  4398046511104 3283 4398046511104
  (BSN.inv_eq_neg_inv_neg
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
          (Enclosure.sfrac false 12 1)))))

noncomputable def p10093 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
      (Enclosure.sfrac false 12 1)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 19459964572603)
    (@Nat.cast.{0} Real Real.instNatCast 4398046511104))
  false

noncomputable def p10094 :=
nat_lit 2738746537431872098101907265

noncomputable def p10095 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
      (Enclosure.sfrac false 12 1)))
  false p10094

noncomputable def p10096 :=
nat_lit 1106455696082897422195850463

noncomputable def p10097 :=
@Enclosure.Real.IsNear.subLit_ff_p p9777 (Enclosure.sfrac false 12 1)
  55873707687371 4398046511104 41 4398046511104 12 1
  0

noncomputable def p10098 :=
@p9984
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 101408700 100000)
    (@Inv.inv.{0} Real Real.instInv
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)))
  false 709831331444944617

noncomputable def p10099 :=
@p10098 4398046511104000 1014087 4398046511104000
  (BSN.t_div_two_pi_mk
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
      true 5)
    101408700 100000
    (Enclosure.sfrac_ofScientific_eq 101408700 5 100000 (Eq.refl true)))

noncomputable def p10100 :=
@p9987 1 699970842191 4398046511104 1 4398046511104
  709831331444944617 4398046511104000 1014087 4398046511104000
  (Enclosure.Real.IsNear.const false 101408700 100000) d145

noncomputable def p10101 :=
@p9983 709831331444944617 4398046511104000 1014087
  4398046511104000 27936853843665 27936853843706 2199023255552
  (p10099 (p10100 (Eq.refl true))) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p10102 :=
@Enclosure.Real.IsNear.recentre' p9777 false 55873707687371 4398046511104
  41 4398046511104 55873707687371 4398046511104 41
  4398046511104
  (p10101 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p10103 :=
@p10017 500000000000000 3097149554123 4398046511104 41
  4398046511104 p10094 p504 p10096
  p2694 d144
  (@p10097 1 3097149554123 3097149554123 4398046511104
    41 4398046511104 (p10102 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p10104 :=
@p10093 19459964572603 4398046511104 259 4398046511104
  true 1247957145620 4398046511104 1 844800000000
  (@p10095 p504 p10096 p2694
    19459964572603 4398046511104 259 4398046511104
    (p10103 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div 19459964572603 4398046511104)

noncomputable def p10105 :=
nat_lit 813255547832324971884944818176

noncomputable def p10106 :=
BSN.cos_reduce2
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 19459964572603)
    (@Nat.cast.{0} Real Real.instNatCast 4398046511104))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast p10105)
    (@Nat.cast.{0} Real Real.instNatCast p2704))
  226375608064910080 72057594037927936 false

noncomputable def p10107 :=
BSN.sin_reduce_arg_pos_rat_q2 19459964572603 4398046511104 226375608064910080
  72057594037927936 0 p10105 p2704 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p10108 :=
nat_lit
  4441961414950679867150723543407001752244072500385309887452271947861765059897565787597881825577503087658146419444931180969939277787534427314113647534924093268254734055916669949530891409456273505210145211889118036458208756669656458251690100596236592764783352849153130496

noncomputable def p10109 :=
nat_lit
  101287475102617973017658420017798503359780011611862664068324537569108749687312607252168039345380143695542539312649194311064959949321131047109436373571615702314236532099297210660057525266048952735162200365677064934881499793785734817096166646796896886289596416

noncomputable def p10110 :=
nat_lit
  45259340154424836115532388749639092486881560710016579272193175204869507773225401754184311173978328705671025977141914780241964916878931555072178594880583534188594588828968847635561622502700167359667816211624802829076926701119468721367141798783605072187452198455833788416

noncomputable def p10111 :=
BSN.cos_dyadic_bound_f 11557056436577184 9007199254740992 5 4
  4398046511104 1691250000001 p10108 p2708
  p10109 p10110 p2711

noncomputable def p10112 :=
@BSN.binarySplit_of_base4 (BSN.cosEvenP 11557056436577184) (BSN.cosEvenQ 9007199254740992)
  0 4 p10108 p2708 p10109
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p10113 :=
p10111 p10109 1247957145620 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p10112 (Eq.refl true))

noncomputable def p10114 :=
@BSN.binarySplit_of_base4 (BSN.cosOddP 11557056436577184) (BSN.cosOddQ 9007199254740992) 0
  4 p10110 p2711 p10109 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p10115 :=
@BSN.cos_arg_round false 1247957145620 4398046511104 p10105
  p2704 11557056436577184 9007199254740992 1691250000001
  1689600000000
  (p10113 (p10114 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p10116 :=
p10106 1247957145620 4398046511104 0 1000000000000000
  1689600000000 844800000000 p10107 BSN.pi_near_15 p10115
  (Eq.refl true) (Eq.refl true)

noncomputable def p10117 :=
@p10011 311989286405 1099511627776 3405780739
  56693568307200000000
  (@p10012 1247957145620 4398046511104 223201246511104
    p2689 311989286405 1099511627776 3405780739
    56693568307200000000
    (p10104 (p10116 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p10118 :=
@p10010 311989286405 1099511627776 3405780739
  56693568307200000000 7749790598830 7749790602113 2199023255552
  p10117 (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p10119 :=
@Enclosure.Real.IsNear.recentre' p10008 false 15499581200943 4398046511104
  3283 4398046511104 15499581200943 4398046511104 3283
  4398046511104
  (p10118 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p10120 :=
nat_lit
  309985050550369108615440589647228077064717599141429085485777251121194219222370421175622061967084488435133551686910882072337069837125

noncomputable def p10121 :=
@Enclosure.Real.IsNear.subLit_tt_n p10084
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p10085
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
        (Enclosure.sfrac false 12 1))))
  p10120 p7305

noncomputable def p10122 :=
nat_lit
  9392121274904992639093198374478657093507512989621251985970364820959788122409942585221153884176282617541451564697747528503557081901003819534720020169201431895305565192546689494679157963

noncomputable def p10123 :=
nat_lit 6475731924053324408570131352313755252347387441476673220773778536984835480695434375

noncomputable def p10124 :=
nat_lit
  41865044450350686657451668328417746011897103230149921733300487623627764511854697869935117842840125253727621741919813387

noncomputable def p10125 :=
nat_lit
  279992884831686465610431474969524171863468649636713823622911754240000000000000000000000000000000000000000000000000000000000000

noncomputable def p10126 :=
nat_lit
  422568464334576690267871620740885727862024295373583846904921307440841121075040103294138257513384311549999952196200227392147074639568752618740103904969354690069702339256915175758818439315675694647363699212288000

noncomputable def p10127 :=
@p10121 p10122 p10090 p10123
  p7342 p10124 p10125 p10126
  p10088 p7305 p10089 p10090

noncomputable def p10128 :=
@Enclosure.Real.IsNear.subLit_tf p10082
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 3 1) p10083)
    (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
        (Enclosure.sfrac false 12 1))))

noncomputable def p10129 :=
nat_lit
  236915485339712990966593355417756795211061261792181477383507987905346145516997939633399055041396839437956766867394560090031011597125

noncomputable def p10130 :=
nat_lit
  9017262966058524654296802315812453816570901732307881519229873722535843944196191648767251481596629486361063933254126559665256935623983306197094340598047239549549247207884412169879157963

noncomputable def p10131 :=
nat_lit 7555215963741741008828922913999055665065050679293003935892184597626192722950233928532622786831282618514375

noncomputable def p10132 :=
nat_lit
  375849121857228388666521440694272798376759165683559808335115782479563300485510593147047703163227197942407657993895196495374016761917320619348988708349

noncomputable def p10133 :=
nat_lit
  88868785551860488240432278881594056622258791041484964153923493121394736478176447756227424530847458869488362100933821960935684630304775510300674530245496264794265316629899972896990788205377165016033688120538616892240084707021739261952000

noncomputable def p10134 :=
@p10128 p10129 p7305 p10130
  p10090 p10131 p5743 p10132
  p9549 p10133 p10120 p7305

noncomputable def p10135 :=
@Enclosure.Real.IsNear.subLit_tf p10080
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 3 1) p10081)
    (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
        (Enclosure.sfrac false 12 1))))

noncomputable def p10136 :=
nat_lit 270433351997082184073694535019792917192865719065650381029357794223728498730798925120288336625

noncomputable def p10137 :=
nat_lit
  455589822016742830591376815960027314697080806213355136762195947757794806040978168548932513516545804638680432924858516907323

noncomputable def p10138 :=
nat_lit
  225412522700721687672782469150079112535218872605578928811459677296444759515467289022913335933191042171128871741588654322706822925125

noncomputable def p10139 :=
nat_lit
  9003426533192303314899730218096488393427678356594096554991530921757367643183553649283578812842222882470990397879214743785620583058414011804940241532416346272365247207884412169879157963

noncomputable def p10140 :=
nat_lit
  15443371743607708082597875149348974802119725792856380084736556886092845517845695623848243172645548948837483266786682294275856153403576013373633622338627268749959082498012639737943932524465267058094728734662651385225412608000

noncomputable def p10141 :=
@p10135 p10136 p5750 p10137
  p5752 p10138 p7305 p10139
  p10090 p10140 p10129 p7305

noncomputable def p10142 :=
@Enclosure.Real.IsNear.subLit_tt_n
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p10077
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p10001 (Enclosure.sfrac false 1 16)))))

noncomputable def p10143 :=
@p10142
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p10079
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 4 1) Real.pi))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p10001 (Enclosure.sfrac false 1 16)))))

noncomputable def p10144 :=
nat_lit 1092175038415168843830501333042815621980227085433404634969824245156408379844491506965558864625

noncomputable def p10145 :=
nat_lit
  112356171183734904668565529312703726786202612228628899051046785695311860662944512515345987296372776064578928924858516907323

noncomputable def p10146 :=
nat_lit 603720443887275331170783875044288744159257734855668875

noncomputable def p10147 :=
nat_lit 2754349858586012015424639949855306727227593286514178728291074720278788551

noncomputable def p10148 :=
nat_lit
  12951184563654492704036575177199097993444414143060243242601413029994508940907996856618476698281229549209385756486315780162237438616841987555328000

noncomputable def p10149 :=
@p10143 p10144 p5750 p10145
  p5752 p10146 p5762 p10147
  p5764 p10148 p10136 p5750

noncomputable def p10150 :=
nat_lit 500934835412089274639875939039669174389452132967763086988720001457927857870642625

noncomputable def p10151 :=
@Enclosure.Real.IsNear.mulLit_ft p10077
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p10001 (Enclosure.sfrac false 1 16))))
  p10150

noncomputable def p10152 :=
nat_lit 1949854276443884476608915253453965956339170004561687425650135640588657532116688112079763471763147119339

noncomputable def p10153 :=
@p10151 p2761 p10152 p5163
  2180273682737 2199023255552 4042538807 28346784153600000000
  p10144 p5750 p10145 p5752

noncomputable def p10154 :=
@Enclosure.Real.IsNear.mulLit_ff p10076
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p10155 :=
nat_lit 630745493011625496125848523063940345308157873720209025

noncomputable def p10156 :=
nat_lit 53633205373748407133774772393138172732159383460982628108778514791

noncomputable def p10157 :=
nat_lit 794194870930066820540419905

noncomputable def p10158 :=
nat_lit 1106436806616965943614995679

noncomputable def p10159 :=
@p10154 p10155 p2767 p10156
  p5168 p10157 p976 p10158
  p5171 p10150 p2761 p10152

noncomputable def p10160 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p10161 :=
@p10160
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p10162 :=
@p10161 p10157 p976 p10158
  p5171 p10157 p976 p10158
  p5171 p10155 p2767 p10156

noncomputable def p10163 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
        (Enclosure.sfrac false 12 1)))
    (Enclosure.sfrac false 1 1))
  884279719003555

noncomputable def p10164 :=
@p10163 140737488355328 1 500000000000000 898126298571
  2199023255552 41 2199023255552 p10157 p976
  p10158 p5171

noncomputable def p10165 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 2 1)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
      (Enclosure.sfrac false 12 1)))
  (Enclosure.sfrac false 1 1) 3097149554123 2199023255552

noncomputable def p10166 :=
@p10165 41 2199023255552 1 1 0 1
  898126298571 898126298571 2199023255552 41 2199023255552

noncomputable def p10167 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 2 1)
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
    (Enclosure.sfrac false 12 1))
  2 1 0 1

noncomputable def p10168 :=
@p10167 3097149554123 4398046511104 41 4398046511104
  3097149554123 2199023255552 41 2199023255552
  (Enclosure.Real.IsNear.const false 2 1)
  (@p10097 1 3097149554123 3097149554123 4398046511104
    41 4398046511104 (p10102 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p10169 :=
@p10162 p5168
  (p10164 d144
    (p10166 (p10168 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (p10164 d144
    (p10166 (p10168 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))

noncomputable def p10170 :=
@p10159 p5163 (p10169 (Eq.refl true))
  (p10164 d144
    (p10166 (p10168 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p10171 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p10001 (Enclosure.sfrac false 1 16))))
  true

noncomputable def p10172 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p10001 (Enclosure.sfrac false 1 16)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Neg.neg.{0} Real Real.instNeg (@Nat.cast.{0} Real Real.instNatCast 1870791586653))
    (@Nat.cast.{0} Real Real.instNatCast 1099511627776))
  true

noncomputable def p10173 :=
nat_lit 4631855620552339529209880294631380822645

noncomputable def p10174 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p10001 (Enclosure.sfrac false 1 16)))
  true p10173

noncomputable def p10175 :=
nat_lit 2343944867489523553583362119095005404333

noncomputable def p10176 :=
nat_lit 5237998249888300836888839

noncomputable def p10177 :=
nat_lit 4029072430273671662182663

noncomputable def p10178 :=
@p10043 (Enclosure.sfrac false 1 16) p10177
  p2793 434286170395031 p2793 1 16 0

noncomputable def p10179 :=
nat_lit 83807971998212813390221424

noncomputable def p10180 :=
nat_lit 9592335360604297706299129

noncomputable def p10181 :=
@Enclosure.Real.IsNear.subLit_ff_n
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
      (Enclosure.sfrac false 12 1))
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
      (Enclosure.sfrac false 12 1)))
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
    (Enclosure.sfrac false 12 1))
  p10180

noncomputable def p10182 :=
nat_lit 17720047944950435961770493504705789952

noncomputable def p10183 :=
@p10181 p2793 253966263439767 p2793
  3097149554123 4398046511104 41 4398046511104 p10182
  p10177 p2793 434286170395031

noncomputable def p10184 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
    (Enclosure.sfrac false 12 1))
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
    (Enclosure.sfrac false 12 1))
  3097149554123 4398046511104 41

noncomputable def p10185 :=
@p10184 4398046511104 3097149554123 4398046511104 41
  4398046511104 p10180 p2793 253966263439767
  p2793
  (@p10097 1 3097149554123 3097149554123 4398046511104
    41 4398046511104 (p10102 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p10186 :=
p10185
  (@p10097 1 3097149554123 3097149554123 4398046511104
    41 4398046511104 (p10102 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p10187 :=
@p10183 p2793 (p10186 (Eq.refl true))
  (@p10097 1 3097149554123 3097149554123 4398046511104
    41 4398046511104 (p10102 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p10188 :=
@p10042 500000000000000 p10176 p2793
  434286170395031 p2793 p10173 p2789
  p10175 p5189 d144
  (@p10178 1 p10179 p10176 p2793
    434286170395031 p2793
    (p10187 (Eq.refl true) (Eq.refl true))
    (Enclosure.Real.IsNear.const false 1 16) (Eq.refl true)
    (Eq.refl true))

noncomputable def p10189 :=
@p10172 1870791586653 1099511627776 311 2199023255552
  true 2180273682737 2199023255552 1 844800000000
  (@p10174 p2789 p10175 p5189
    1870791586653 1099511627776 311 2199023255552
    (p10188 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_true_div 1870791586653 1099511627776)

noncomputable def p10190 :=
nat_lit
  113655224611176249442253087915666642279033475859321387094791147500747602032318516707055145083550816884889246311504169060956253904318847776859475248056289235195240659156965563569995053965027573910458518021441

noncomputable def p10191 :=
nat_lit
  1622802769122764392324106724327719234349212789549269575107433290344039629007054814940083063754292754794492706802961233170588325392823601817223999646799335525777792363665091674232111343495727961276202090496000

noncomputable def p10192 :=
nat_lit
  22511608639570593041219252178691162326786033411040516099240303402324893978528280278352024822716735382828745402580480813273014697169513595639274796196692010125920939312266329797127909426114073011521

noncomputable def p10193 :=
nat_lit
  923896008435174300571026364577044809490897222788773899395055323743384950831504537016390584392257854421526959778350059135433012268347658161485567056886070787574678589580385837728024450624723311533663745025345

noncomputable def p10194 :=
nat_lit
  92499757839997570362474083286679996357905129004308365781123697549610258853402124451584734633994687023286084287768790290723534547390945303581767979867562124969334164728910225431230346579256493792743519158272000

noncomputable def p10195 :=
BSN.sin_dyadic_bound_f 1870791586653 1099511627776 5 4 2199023255552
  844800000000 p10190 p10191 p10192
  p10193 p10194

noncomputable def p10196 :=
@BSN.binarySplit_of_base4 (BSN.sinEvenP 1870791586653) (BSN.sinEvenQ 1099511627776) 0
  4 p10190 p10191 p10192 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p10197 :=
p10195 p10192 2180273682737 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p10196 (Eq.refl true))

noncomputable def p10198 :=
@BSN.binarySplit_of_base4 (BSN.sinOddP 1870791586653) (BSN.sinOddQ 1099511627776) 0
  4 p10193 p10194 p10192 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p10199 :=
p10189
  (BSN.sin_neg_of_bound 1870791586653 1099511627776 false 2180273682737
    2199023255552 1 844800000000
    (p10197 (p10198 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p10200 :=
p10153 p10170
  (@p10171 2180273682737 2199023255552 264931823255552
    p3422 2180273682737 2199023255552 4042538807
    28346784153600000000 (p10199 (Eq.refl true))
    (Eq.refl true))

noncomputable def p10201 :=
nat_lit 2106871251900312358454586987847283663286825

noncomputable def p10202 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p10079
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 4 1) Real.pi))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p10001 (Enclosure.sfrac false 1 16))))
  p10201

noncomputable def p10203 :=
nat_lit 89575785876382715212136585364445229235298151759680779

noncomputable def p10204 :=
@p10202 p2820 p10203 p5216
  286548332435 2199023255552 4042538807 28346784153600000000
  p10146 p5762 p10147 p5764

noncomputable def p10205 :=
nat_lit 2382584612790200461621259715

noncomputable def p10206 :=
nat_lit 3319310419850897830844987037

noncomputable def p10207 :=
@Enclosure.Real.IsNear.mulLit_ff p10079
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 4 1) Real.pi)
  p10205 p976 p10206 p5171

noncomputable def p10208 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 3 1)
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p10209 :=
@p10208 3 1 0 1 p10157
  p976 p10158 p5171 p10205
  p976 p10206

noncomputable def p10210 :=
@p10209 p5171 (Enclosure.Real.IsNear.const false 3 1)
  (p10164 d144
    (p10166 (p10168 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p10211 :=
@p10207 884279719003555 70368744177664 1 250000000000000
  p10201 p2820 p10203 p5216
  p10210 d146 (Eq.refl true)

noncomputable def p10212 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p10001 (Enclosure.sfrac false 1 16)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Neg.neg.{0} Real Real.instNeg (@Nat.cast.{0} Real Real.instNatCast 1870791586653))
    (@Nat.cast.{0} Real Real.instNatCast 1099511627776))
  true

noncomputable def p10213 :=
@p10212 1870791586653 1099511627776 311 2199023255552
  true 286548332435 2199023255552 1 844800000000
  (@p10174 p2789 p10175 p5189
    1870791586653 1099511627776 311 2199023255552
    (p10188 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_true_div 1870791586653 1099511627776)

noncomputable def p10214 :=
nat_lit
  33501992045364307628160310336455065826882623866383939866011434007422601057270161546485290830145422167120082893379392006367029286743278932916481496550290155411645137535194460292804728456872106274397654164801

noncomputable def p10215 :=
nat_lit
  95458986418986140724947454372218778491130164091133504418084311196708213471003224408240180220840750282028982753115366657093430905460211871601411743929372677986928962568534804366594784911513409486835417088000

noncomputable def p10216 :=
nat_lit
  340588456559764579716712313539332488699079630043776256615320827593021435091311572552181502467955036950395049314106189803911326748107658695878148002596998140505956196520391875247712794243371933915282516813121

noncomputable def p10217 :=
nat_lit
  14605224922104879530916960518949473109142915105943426175966899613096356661063493334460747573788634793150434361226651098535294928535412416355015996821194019732000131272985825068089002091461551651485818814464000

noncomputable def p10218 :=
BSN.cos_dyadic_bound_t 1870791586653 1099511627776 5 4 2199023255552
  844800000000 p10214 p10215 p10192
  p10216 p10217

noncomputable def p10219 :=
@BSN.binarySplit_of_base4 (BSN.cosEvenP 1870791586653) (BSN.cosEvenQ 1099511627776) 0
  4 p10214 p10215 p10192 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p10220 :=
p10218 p10192 286548332435 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p10219 (Eq.refl true))

noncomputable def p10221 :=
@BSN.binarySplit_of_base4 (BSN.cosOddP 1870791586653) (BSN.cosOddQ 1099511627776) 0
  4 p10216 p10217 p10192 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p10222 :=
p10213
  (BSN.cos_neg_of_bound 1870791586653 1099511627776 true 286548332435
    2199023255552 1 844800000000
    (p10220 (p10221 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p10223 :=
p10204 p10211
  (@p10036 286548332435 2199023255552 264931823255552
    p3422 286548332435 2199023255552 4042538807
    28346784153600000000 (p10222 (Eq.refl true))
    (Eq.refl true))

noncomputable def p10224 :=
nat_lit 5593877331123011585339557425

noncomputable def p10225 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 3 1) p10081)
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
      (Enclosure.sfrac false 12 1)))
  p10224

noncomputable def p10226 :=
nat_lit 91909122826706000389940459799126613

noncomputable def p10227 :=
nat_lit 40296293493348464835482746819945229196071573670136734018059397235471917007667595896103629629259477454165

noncomputable def p10228 :=
nat_lit
  12269132921327423218348293806925974536689644221037852768359814213546746318935939973285321521717027772312424916810053441904510515549065413527

noncomputable def p10229 :=
nat_lit
  17872305146858502559137971851652300530690092691204284921657953937609472844139411916531433472000000000000000000000000000000000000000000000000000000

noncomputable def p10230 :=
@p10225 p976 p10226 p2846
  p10227 p7449 p10228 p10229
  p10138 p7305 p10139 p10090

noncomputable def p10231 :=
nat_lit 1864625777041003861779852475

noncomputable def p10232 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 3 1) p10081
  3 1 0 1 p10231 p976

noncomputable def p10233 :=
@Enclosure.Real.IsNear.neg
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
          (Enclosure.sfrac false 12 1)))))

noncomputable def p10234 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
        (Enclosure.sfrac false 12 1))))
  884279719003555

noncomputable def p10235 :=
@p10234 140737488355328 1 500000000000000 2108637953545
  2199023255552 3405780739 56693568307200000000 p10231
  p976 p10226 p2854

noncomputable def p10236 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
        (Enclosure.sfrac false 12 1))))
  true

noncomputable def p10237 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
      (Enclosure.sfrac false 12 1)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 19459964572603)
    (@Nat.cast.{0} Real Real.instNatCast 4398046511104))
  false

noncomputable def p10238 :=
@p10237 19459964572603 4398046511104 259 4398046511104
  true 4217275907090 4398046511104 1 844800000000
  (@p10095 p504 p10096 p2694
    19459964572603 4398046511104 259 4398046511104
    (p10103 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div 19459964572603 4398046511104)

noncomputable def p10239 :=
BSN.sin_reduce2
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 19459964572603)
    (@Nat.cast.{0} Real Real.instNatCast 4398046511104))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast p10105)
    (@Nat.cast.{0} Real Real.instNatCast p2704))
  226375608064910080 72057594037927936 false

noncomputable def p10240 :=
nat_lit
  15091853757065260946086552173763544052602890604075698309859044268014627677882440718002022177143682483070730601550753030957382083273725372938926328026914021779340230975918343167601607276089582457956710434968069867140184869087320621140820056406323479515170158678466625536

noncomputable def p10241 :=
nat_lit
  667582338056245438668675204243831465490055283667469306154654509566051430133217024886826934189239674826355612291082932194574739779164547370092820033133599058893972435570631754625040768847067634603862769061368439492849485366996890270651430752103684361693971810642558976000

noncomputable def p10242 :=
nat_lit
  122822766184612489352197595448922540180554706617820431555074383768987003881816534598533776390899467923524876024898160530899211708721436577088590646969795015893410707965252990872285967577200604068022209894264136860774645253425540153101335419643075393557000852621418823680

noncomputable def p10243 :=
nat_lit
  38052193269205990004114486641898393532933151169045750450815307045264931517593370418549135248786661465102269900591727135090760167412379200095290741888615146356956428827526010013627323824282855172420177836498001051092420665918822745427131552869910008616556393206625861632000

noncomputable def p10244 :=
BSN.sin_dyadic_bound_f 11557056436577184 9007199254740992 5 4
  4398046511104 1691250000001 p10240 p10241
  p10109 p10242 p10243

noncomputable def p10245 :=
@BSN.binarySplit_of_base4 (BSN.sinEvenP 11557056436577184) (BSN.sinEvenQ 9007199254740992)
  0 4 p10240 p10241 p10109
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p10246 :=
p10244 p10109 4217275907090 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p10245 (Eq.refl true))

noncomputable def p10247 :=
@BSN.binarySplit_of_base4 (BSN.sinOddP 11557056436577184) (BSN.sinOddQ 9007199254740992) 0
  4 p10242 p10243 p10109 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p10248 :=
@BSN.sin_arg_round false 4217275907090 4398046511104 p10105
  p2704 11557056436577184 9007199254740992 1691250000001
  1689600000000
  (p10246 (p10247 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p10249 :=
p10239 4217275907090 4398046511104 0 1000000000000000
  1689600000000 844800000000 p10107 BSN.pi_near_15 p10248
  (Eq.refl true) (Eq.refl true)

noncomputable def p10250 :=
p10235 d144
  (@p10236 4217275907090 4398046511104 223201246511104
    p2689 2108637953545 2199023255552 3405780739
    56693568307200000000
    (p10238 (p10249 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p10251 :=
@Neg.neg.{0} Real Real.instNeg
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p10076
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p10001 (Enclosure.sfrac false 1 16)))))

noncomputable def p10252 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p10251
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 4 1) Real.pi)
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p10001 (Enclosure.sfrac false 1 16)))))

noncomputable def p10253 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p10252
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) p10081)
    (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
        (Enclosure.sfrac false 12 1))))

noncomputable def p10254 :=
@Enclosure.Real.IsNear.of_eq
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
      (Enclosure.sfrac false 12 1)))
  (p10000
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p10253
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p10083
        (Zeta.RiemannSiegel.correction
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
            (Enclosure.sfrac false 12 1))))))

noncomputable def p10255 :=
@p10004
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p10253
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p10083
      (Zeta.RiemannSiegel.correction
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
          (Enclosure.sfrac false 12 1)))))
  15499581200943

noncomputable def p10256 :=
nat_lit 2599831116139887966325363195471398395121930454710399117059207436397383717383593761269556155

noncomputable def p10257 :=
nat_lit
  790479804733422271828191557379506970456939623395341697719174672007715867409351766759820535462420398074357656865877868590516327

noncomputable def p10258 :=
nat_lit
  4063691709884211049743037586188688813010706483329223583873034371574584120967168000000000000000000000000000000000000000000000000000000

noncomputable def p10259 :=
@p10255 4398046511104 3283 4398046511104 p10256
  p7478 p10257 p10258 p10227
  p7449 p10228 p10229

noncomputable def p10260 :=
nat_lit 7879329552884416035727880015912699728501440821099522258580218158661267806782713867704523845

noncomputable def p10261 :=
@Enclosure.Real.IsNear.subLit_ff_n p10253
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p10083
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
        (Enclosure.sfrac false 12 1))))
  p10260 p7478

noncomputable def p10262 :=
nat_lit
  758747400244031578993813926413832334609948257599069285597819238702576257296979553666369587550335566726636522595351609390516327

noncomputable def p10263 :=
nat_lit 1083519817655639885835859670060925702541752131180754515870288525625

noncomputable def p10264 :=
nat_lit 127265114100919460260321401450066355644751602063683671953762236786334888978991340669330193409

noncomputable def p10265 :=
nat_lit 16297730898466337565939842896159049814070379922440847360000000000000000000000000000000000000000000000

noncomputable def p10266 :=
nat_lit
  547588345583828910226493071061814993885304933347359369563763348967334521778720564434051165616748955841312239814124442684128634077875919934000094349791068160

noncomputable def p10267 :=
@p10261 p10262 p10258 p10263
  p5882 p10264 p10265 p10266
  p10256 p7478 p10257 p10258

noncomputable def p10268 :=
@Enclosure.Real.IsNear.subLit_ff_p p10252
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) p10081)
    (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
        (Enclosure.sfrac false 12 1))))

noncomputable def p10269 :=
nat_lit 2804958298405389275120052724590464246795471261102959751104173949715

noncomputable def p10270 :=
nat_lit 2368111090784670268972315825318353804802257319343533478259418720766285928152462102279

noncomputable def p10271 :=
nat_lit 19248562526192310584051881760478735174267343986457972049620892565616483548788399160486994875

noncomputable def p10272 :=
nat_lit
  747330165886926352197150331560233992003029685122169886977241016620280086791360808606787426093473804838535187555351609390516327

noncomputable def p10273 :=
nat_lit
  1659580504052091819723620812334276460187386236185136178918825545018868075267712842036714399277028306584227133134330554411846748802915293271945268862742691840

noncomputable def p10274 :=
@p10268 p10269 p5882 p10270
  p5884 p10271 p7478 p10272
  p10258 p10273 p10260 p7478

noncomputable def p10275 :=
@Enclosure.Real.IsNear.subLit_ft p10251
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 4 1) Real.pi)
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p10001 (Enclosure.sfrac false 1 16)))))

noncomputable def p10276 :=
nat_lit 180739069213373231983591447183379742828370714916241205873387225875

noncomputable def p10277 :=
nat_lit 2572808173904513510489742599191463042924180955227515891424338370239465784457386306837

noncomputable def p10278 :=
nat_lit 1927971799521520383845130035

noncomputable def p10279 :=
nat_lit 109092498510577547525985795039602369

noncomputable def p10280 :=
nat_lit 434046273265227625916476188422262958444300556920919908931217771588444021689137808451064299520

noncomputable def p10281 :=
@p10275 p10276 p5882 p10277
  p5892 p10278 p982 p10279
  p3486 p10280 p10269 p5882

noncomputable def p10282 :=
@Enclosure.Real.IsNear.neg
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p10076
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p10001 (Enclosure.sfrac false 1 16)))))

noncomputable def p10283 :=
@Enclosure.Real.IsNear.mulLit_ft p10076
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p10001 (Enclosure.sfrac false 1 16))))
  p10155

noncomputable def p10284 :=
@p10283 p2767 p10156 p5168
  286548332435 2199023255552 4042538807 28346784153600000000
  p10276 p5882 p10277 p5892

noncomputable def p10285 :=
p10284 (p10169 (Eq.refl true))
  (@p10036 286548332435 2199023255552 264931823255552
    p3422 286548332435 2199023255552 4042538807
    28346784153600000000 (p10222 (Eq.refl true))
    (Eq.refl true))

noncomputable def p10286 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 4 1) Real.pi)
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p10001 (Enclosure.sfrac false 1 16))))
  884279719003555

noncomputable def p10287 :=
@p10286 70368744177664 1 250000000000000 2180273682737
  2199023255552 4042538807 28346784153600000000 p10278
  p982 p10279 p3486

noncomputable def p10288 :=
p10287 d146
  (@p10171 2180273682737 2199023255552 264931823255552
    p3422 2180273682737 2199023255552 4042538807
    28346784153600000000 (p10199 (Eq.refl true))
    (Eq.refl true))

noncomputable def p10289 :=
@p10274 p10262 p10258
  (@p10281 p10270 p5884
    (@p10282 true p10276 p5882 p10277
      p5892 (p10285 (Eq.refl true)))
    (p10288 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p10290 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 2 1) p10081)
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
      (Enclosure.sfrac false 12 1)))
  p10231

noncomputable def p10291 :=
nat_lit 10323016426780324964550264676624811826274028326495317722448360705

noncomputable def p10292 :=
nat_lit 1015538848042947841371193172184780855651090011725694486315901266805553596808886383

noncomputable def p10293 :=
nat_lit 66755505760118118670089596502667468038432276162317710786560000000000000000000000000000000

noncomputable def p10294 :=
@p10290 p982 p10226 p2908
  p10291 p5277 p10292 p10293
  p10271 p7478 p10272 p10258

noncomputable def p10295 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 2 1) p10081
  2 1 0 1 p10231 p976

noncomputable def p10296 :=
@Neg.neg.{0} Real Real.instNeg
  (p10075
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p10001 (Enclosure.sfrac false 1 16)))))

noncomputable def p10297 :=
@Enclosure.Real.IsNear.of_eq
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
      (Enclosure.sfrac false 12 1)))
  (p10000
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p10296
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p10081
        (Zeta.RiemannSiegel.correction
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
            (Enclosure.sfrac false 12 1))))))

noncomputable def p10298 :=
@p10004
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p10296
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p10081
      (Zeta.RiemannSiegel.correction
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
          (Enclosure.sfrac false 12 1)))))
  15499581200943

noncomputable def p10299 :=
nat_lit 666019055156939917546757349442333296447384528553935

noncomputable def p10300 :=
nat_lit 64805027646153833645997797273866522510526441135808968521046781545083

noncomputable def p10301 :=
nat_lit 15178444700749905375707748249321291050007920640000000000000000000000000000000

noncomputable def p10302 :=
@p10298 4398046511104 3283 4398046511104 p10299
  p7523 p10300 p10301 p10291
  p5277 p10292 p10293

noncomputable def p10303 :=
nat_lit 1731562176053533171201153782838729679985

noncomputable def p10304 :=
@Enclosure.Real.IsNear.subLit_ff_n p10296
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p10081
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
        (Enclosure.sfrac false 12 1))))
  p10303 p5917

noncomputable def p10305 :=
nat_lit 129075131585000336087188513143803436000992471203

noncomputable def p10306 :=
nat_lit 8281510042308831696680324873035580034592788197607375

noncomputable def p10307 :=
nat_lit 57487297856878788889103818129145097395194110862668759063485181545083

noncomputable def p10308 :=
nat_lit 453269081006501163512432592340815225123279575119047241864222520033977531262726553961758720

noncomputable def p10309 :=
@p10304 p10305 p5920 p10306
  p7523 p10307 p10301 p10308
  p10299 p7523 p10300 p10301

noncomputable def p10310 :=
@Enclosure.Real.IsNear.neg
  (p10075
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p10001 (Enclosure.sfrac false 1 16)))))

noncomputable def p10311 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p10312 :=
@p10311
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p10001 (Enclosure.sfrac false 1 16))))
  p10157

noncomputable def p10313 :=
@p10312 p976 p10158 p5171
  2180273682737 2199023255552 4042538807 28346784153600000000
  p10303 p5917 p10305 p5920

noncomputable def p10314 :=
p10313
  (p10164 d144
    (p10166 (p10168 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (@p10171 2180273682737 2199023255552 264931823255552
    p3422 2180273682737 2199023255552 4042538807
    28346784153600000000 (p10199 (Eq.refl true))
    (Eq.refl true))

noncomputable def p10315 :=
@Enclosure.Real.IsNear.mulLit_ff p10081
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
      (Enclosure.sfrac false 12 1)))
  p10231 p976 p10226

noncomputable def p10316 :=
nat_lit 4441379146571091299486205

noncomputable def p10317 :=
nat_lit 124670475147758633641574400000000

noncomputable def p10318 :=
@p10004
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p10001 (Enclosure.sfrac false 1 16))))
  15499581200943

noncomputable def p10319 :=
@p10318 4398046511104 3283 4398046511104 286548332435
  2199023255552 4042538807 28346784153600000000 p10316
  p7541 74784361552392125914007 p10317

noncomputable def p10320 :=
p10319
  (p10092
    (@Enclosure.Real.IsNear.neg p10008 false 15499581200943 4398046511104
      3283 4398046511104 (p10119 (Eq.refl true))))
  (@p10036 286548332435 2199023255552 264931823255552
    p3422 286548332435 2199023255552 4042538807
    28346784153600000000 (p10222 (Eq.refl true))
    (Eq.refl true))

noncomputable def p10321 :=
@p10315 p2854 p10316 p7541
  74784361552392125914007 p10317 p10306 p7523
  p10307 p10301
  (@p10233 true p10231 p976 p10226
    p2854 (p10250 (Eq.refl true)))
  (@p10002 false p10316 p7541
    74784361552392125914007 p10317
    (BSN.correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
        (Enclosure.sfrac false 12 1))
      (p10003 (Eq.refl true) (Eq.refl true)
        (p9780 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p10320 (Eq.refl true)))

noncomputable def p10322 :=
p10302
  (p10092
    (@Enclosure.Real.IsNear.neg p10008 false 15499581200943 4398046511104
      3283 4398046511104 (p10119 (Eq.refl true))))
  (p10309
    (@p10310 true p10303 p5917 p10305
      p5920 (p10314 (Eq.refl true)))
    (p10321 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p10323 :=
p10294
  (@p10295 p10226 p2854 p10231
    p982 p10226 p2908
    (Enclosure.Real.IsNear.const false 2 1)
    (@p10233 true p10231 p976 p10226
      p2854 (p10250 (Eq.refl true)))
    (Eq.refl true))
  (@p10297 false p10291 p5277 p10292
    p10293
    (BSN.deriv_correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
        (Enclosure.sfrac false 12 1))
      (p10003 (Eq.refl true) (Eq.refl true)
        (p9780 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p10322 (Eq.refl true)))

noncomputable def p10324 :=
nat_lit 243960216387325813961545990205987768550125

noncomputable def p10325 :=
nat_lit 2480261375680050707895202798368232959795710565720928941418771

noncomputable def p10326 :=
@Enclosure.Real.IsNear.mulLit_ff p10083
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
      (Enclosure.sfrac false 12 1)))
  p10324 p2820 p10325

noncomputable def p10327 :=
@Enclosure.Real.IsNear.neg
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 4 1)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
          (Enclosure.sfrac false 12 1)))))

noncomputable def p10328 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 4 1)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
        (Enclosure.sfrac false 12 1))))
  p1068

noncomputable def p10329 :=
@p10328 p1070 p1071 p1072 311989286405
  1099511627776 3405780739 56693568307200000000 p10324
  p2820 p10325 p2961

noncomputable def p10330 :=
p10329 d148
  (@p10012 1247957145620 4398046511104 223201246511104
    p2689 311989286405 1099511627776 3405780739
    56693568307200000000
    (p10104 (p10116 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p10331 :=
@p10326 p2961 p10316 p7541
  74784361552392125914007 p10317 p10263 p5882
  p10264 p10265
  (@p10327 true p10324 p2820 p10325
    p2961 (p10330 (Eq.refl true)))
  (@p10002 false p10316 p7541
    74784361552392125914007 p10317
    (BSN.correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
        (Enclosure.sfrac false 12 1))
      (p10003 (Eq.refl true) (Eq.refl true)
        (p9780 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p10320 (Eq.refl true)))

noncomputable def p10332 :=
p10259
  (p10092
    (@Enclosure.Real.IsNear.neg p10008 false 15499581200943 4398046511104
      3283 4398046511104 (p10119 (Eq.refl true))))
  (p10267
    (p10289 (p10323 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true))
    (p10331 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p10333 :=
p10230
  (@p10232 p10226 p2854 p10224
    p976 p10226 p2846
    (Enclosure.Real.IsNear.const false 3 1)
    (@p10233 true p10231 p976 p10226
      p2854 (p10250 (Eq.refl true)))
    (Eq.refl true))
  (@p10254 false p10227 p7449 p10228
    p10229
    (BSN.iteratedDeriv_two_correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
        (Enclosure.sfrac false 12 1))
      (p10003 (Eq.refl true) (Eq.refl true)
        (p9780 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p10332 (Eq.refl true)))

noncomputable def p10334 :=
@p10141 p10130 p10090
  (@p10149 p10137 p5752
    (p10200 (Eq.refl true)) (p10223 (Eq.refl true))
    (Eq.refl true) (Eq.refl true))
  (p10333 (Eq.refl true)) (Eq.refl true) (Eq.refl true)

noncomputable def p10335 :=
nat_lit 731880649161977441884637970617963305650375

noncomputable def p10336 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 3 1) p10083)
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
      (Enclosure.sfrac false 12 1)))
  p10335

noncomputable def p10337 :=
@p10336 p2820 p10325 p2972
  p10291 p5277 p10292 p10293
  p10131 p5743 p10132 p9549

noncomputable def p10338 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 3 1) p10083
  3 1 0 1 p10324 p2820

noncomputable def p10339 :=
p10337
  (@p10338 p10325 p2961 p10335
    p2820 p10325 p2972
    (Enclosure.Real.IsNear.const false 3 1)
    (@p10327 true p10324 p2820 p10325
      p2961 (p10330 (Eq.refl true)))
    (Eq.refl true))
  (@p10297 false p10291 p5277 p10292
    p10293
    (BSN.deriv_correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
        (Enclosure.sfrac false 12 1))
      (p10003 (Eq.refl true) (Eq.refl true)
        (p9780 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p10322 (Eq.refl true)))

noncomputable def p10340 :=
nat_lit 1458045285112132021521791872626457148109799916992825361875

noncomputable def p10341 :=
nat_lit 66933339477469268581770804782053919818333890850344620868344580621477307319928510479557

noncomputable def p10342 :=
@Enclosure.Real.IsNear.mulLit_tf p10085
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
      (Enclosure.sfrac false 12 1)))
  p10340 p2977 p10341

noncomputable def p10343 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 8 1)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi) Real.pi))
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
        (Enclosure.sfrac false 12 1))))

noncomputable def p10344 :=
@p10343 p1059 p1061 p1062
  p1063 2108637953545 2199023255552 3405780739
  56693568307200000000 p10340 p2977 p10341

noncomputable def p10345 :=
@p10344 p2980 d149
  (@p10236 4217275907090 4398046511104 223201246511104
    p2689 2108637953545 2199023255552 3405780739
    56693568307200000000
    (p10238 (p10249 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p10346 :=
@p10342 p2980 p10316 p7541
  74784361552392125914007 p10317 p10123 p7342
  p10124 p10125 (p10345 (Eq.refl true))
  (@p10002 false p10316 p7541
    74784361552392125914007 p10317
    (BSN.correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
        (Enclosure.sfrac false 12 1))
      (p10003 (Eq.refl true) (Eq.refl true)
        (p9780 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p10320 (Eq.refl true)))

noncomputable def p10347 :=
p10091
  (p10092
    (@Enclosure.Real.IsNear.neg p10008 false 15499581200943 4398046511104
      3283 4398046511104 (p10119 (Eq.refl true))))
  (p10127
    (@p10134 p10122 p10090 p10334
      (p10339 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true))
    (p10346 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p10348 :=
@p10074 p10067
  (@p10086 false p10071 p7287 p10072
    p10073
    (BSN.iteratedDeriv_three_correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
        (Enclosure.sfrac false 12 1))
      (p10003 (Eq.refl true) (Eq.refl true)
        (p9780 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p10347 (Eq.refl true)))

noncomputable def p10349 :=
@p10065 p10066 p10067 676148647 8589934592
  1 8589934592 p9996 p9972 p9997
  p9974
  (@p10069 p7279 p10066 p10067
    (BSN.correctionLinear_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p9777
        (Enclosure.sfrac false 12 1)))
    (@Enclosure.Real.IsNear.neg p10068 false p10064 p7279
      p10066 p10067
      (p10348 d150 (Eq.refl true))))

noncomputable def p10350 :=
@Enclosure.Real.IsNear.recentre' (@Inv.inv.{0} Real Real.instInv p9777) false
  1352297294 17179869184 2 17179869184 676148647 8589934592

noncomputable def p10351 :=
@Enclosure.Real.IsNear.inv_image p9777 218256670681 17179869184 41
  17179869184 676148646 676148648 8589934592
  (p9990 (Eq.refl true)) (Eq.refl true) (Eq.refl true)

noncomputable def p10352 :=
p10063
  (p10349
    (@p10350 1 8589934592
      (p10351 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (Eq.refl true))
    (Eq.refl true))

noncomputable def p10353 :=
@p9975 p9772
  (@p9977 8589934592
    (@p2563 1 0 1
      (BSN.neg_one_pow_even_mk 12 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1))
    p9993 (Eq.refl true))
  (p10352 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p10354 :=
@p9779 p9769 p9771 p9772
  (BSN.hardyZApproximantRS_eq
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
      true 5)
    12
    (p9780 (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (p9969 p10353 (Eq.refl true) (Eq.refl true))

theorem d185 : p9770 p9771 p9772 :=
@p9773 p9769 p9771 p9772
  (@Eq.refl.{1} Real
    (hardyZApproximantRS
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
        true 5)))
  p10354

noncomputable def p10355 :=
Enclosure.Real.IsNear
  (hardyZErrorBoundRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
      true 5))
  false 5981927491 549755813888

noncomputable def p10356 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Real.sqrt p9190)
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p10357 :=
@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 25 4) (@Inv.inv.{0} Real Real.instInv p10356))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 1 32)
    (@Inv.inv.{0} Real Real.instInv
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p10356
          p10356)
        p10356)))

noncomputable def p10358 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZErrorBoundRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
      true 5))
  p10357 false 5981927491

noncomputable def p10359 :=
BSN.hardyZErrorBoundRS_mk
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
    true 5)
  101285400 100000
  (Enclosure.sfrac_ofScientific_eq 101285400 5 100000 (Eq.refl true))
  (Eq.refl true)

noncomputable def p10360 :=
@Enclosure.Real.IsNear.addLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 25 4) (@Inv.inv.{0} Real Real.instInv p10356))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 1 32)
    (@Inv.inv.{0} Real Real.instInv
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p10356
          p10356)
        p10356)))

noncomputable def p10361 :=
@p10360 747740925 68719476736 25 68719476736 91
  549755813888 1 549755813888 411074927054213349376 5981927491
  549755813888

noncomputable def p10362 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 25 4)
  (@Inv.inv.{0} Real Real.instInv p10356) 25 4 0 1
  29909637 17179869184

noncomputable def p10363 :=
@Enclosure.Real.IsNear.recentre' (@Inv.inv.{0} Real Real.instInv p10356) false 29909637
  17179869184 1 17179869184 29909637 17179869184

noncomputable def p10364 :=
nat_lit 8476536445495750574600427

noncomputable def p10365 :=
@Enclosure.Real.IsNear.mulLit_ff (Real.sqrt p9190)
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p10366 :=
@p10365 30607763835 8589934592 3 8589934592
  1384703647608981 8589934592000 506427 8589934592000 p10364
  14757395258967641292800 19654708960013769

noncomputable def p10367 :=
@p10366 73786976294838206464000
  (p9391
    (p9400 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (p9395 (p9397 (Eq.refl true))) (Eq.refl true)

noncomputable def p10368 :=
@Enclosure.Real.IsNear.inv_image p10356 p10364 14757395258967641292800
  19654708960013769 73786976294838206464000 14954818 14954819
  8589934592 p10367 (Eq.refl true) (Eq.refl true)

noncomputable def p10369 :=
@p10361 201 549755813888
  (@p10362 1 17179869184 747740925 68719476736 25
    68719476736 (Enclosure.Real.IsNear.const false 25 4)
    (@p10363 1 17179869184
      (p10368 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (Eq.refl true))
    (Eq.refl true))

noncomputable def p10370 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 1 32)
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p10356
        p10356)
      p10356))
  1

noncomputable def p10371 :=
@p10370 32 0 1 91 17179869184 1
  17179869184 91 549755813888 1 549755813888

noncomputable def p10372 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p10356
        p10356)
      p10356))
  false

noncomputable def p10373 :=
nat_lit 609053300372560751239924425935012064298909010937499946604161689508808054483

noncomputable def p10374 :=
@Enclosure.Real.IsNear.inv_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p10356
      p10356)
    p10356)
  p10373 p6020

noncomputable def p10375 :=
nat_lit 105916774874520570055574106950708912808191569323353582227252490672889

noncomputable def p10376 :=
nat_lit 401734511064747568885490523085290650630550748445698208825344000000000

noncomputable def p10377 :=
nat_lit 71851670111817733651706190188340683536150708582329

noncomputable def p10378 :=
nat_lit 1666038568637993523211267452639216602378991

noncomputable def p10379 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p10356
    p10356)
  p10356 p10377 p6024 p10378

noncomputable def p10380 :=
nat_lit 5444517870735015415413993718908291383296000000

noncomputable def p10381 :=
@Enclosure.Real.IsNear.mulLit_ff p10356 p10356 p10364
  14757395258967641292800 19654708960013769 73786976294838206464000
  p10364 14757395258967641292800 19654708960013769
  73786976294838206464000 p10377

noncomputable def p10382 :=
@p10379 p10380 p10364 14757395258967641292800
  19654708960013769 73786976294838206464000 p10373 p6020
  p10375 p10376
  (@p10381 p6024 p10378 p10380
    p10367 p10367 (Eq.refl true))
  p10367

noncomputable def p10383 :=
@p10374 p10375 p10376 45 46
  8589934592 (p10382 (Eq.refl true)) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p10384 :=
p10371 (Enclosure.Real.IsNear.const false 1 32)
  (@p10372 91 17179869184 1 17179869184 91
    17179869184 1 17179869184 (p10383 (Eq.refl true))
    (Eq.refl true))

theorem d186 : p10355 201 549755813888 :=
@p10358 549755813888 201 549755813888
  (p10359 (Eq.refl true))
  (p10369 (p10384 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p10385 :=
Enclosure.Real.IsNear
  (hardyZErrorBoundRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
      true 5))
  false 5972837091 549755813888

noncomputable def p10386 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Real.sqrt p9777)
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p10387 :=
@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 25 4) (@Inv.inv.{0} Real Real.instInv p10386))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 1 32)
    (@Inv.inv.{0} Real Real.instInv
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p10386
          p10386)
        p10386)))

noncomputable def p10388 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZErrorBoundRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
      true 5))
  p10387 false 5972837091

noncomputable def p10389 :=
BSN.hardyZErrorBoundRS_mk
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
    true 5)
  101408700 100000
  (Enclosure.sfrac_ofScientific_eq 101408700 5 100000 (Eq.refl true))
  (Eq.refl true)

noncomputable def p10390 :=
@Enclosure.Real.IsNear.addLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 25 4) (@Inv.inv.{0} Real Real.instInv p10386))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 1 32)
    (@Inv.inv.{0} Real Real.instInv
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p10386
          p10386)
        p10386)))

noncomputable def p10391 :=
@p10390 746604625 68719476736 25 68719476736 91
  549755813888 1 549755813888 410450239522892414976 5972837091
  549755813888

noncomputable def p10392 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 25 4)
  (@Inv.inv.{0} Real Real.instInv p10386) 25 4 0 1
  29864185 17179869184

noncomputable def p10393 :=
@Enclosure.Real.IsNear.recentre' (@Inv.inv.{0} Real Real.instInv p10386) false 29864185
  17179869184 1 17179869184 29864185 17179869184

noncomputable def p10394 :=
nat_lit 33957748280347118897200797

noncomputable def p10395 :=
@Enclosure.Real.IsNear.mulLit_ff (Real.sqrt p9777)
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p10396 :=
@p10395 61234149385 17179869184 7 17179869184
  2772778639157961 17179869184000 1014087 17179869184000
  p10394 59029581035870565171200 81506205328590831

noncomputable def p10397 :=
@p10396 295147905179352825856000
  (p9982
    (p9991 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (p9986 (p9988 (Eq.refl true))) (Eq.refl true)

noncomputable def p10398 :=
@Enclosure.Real.IsNear.inv_image p10386 p10394 59029581035870565171200
  81506205328590831 295147905179352825856000 14932092 14932093
  8589934592 p10397 (Eq.refl true) (Eq.refl true)

noncomputable def p10399 :=
@p10391 201 549755813888
  (@p10392 1 17179869184 746604625 68719476736 25
    68719476736 (Enclosure.Real.IsNear.const false 25 4)
    (@p10393 1 17179869184
      (p10398 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (Eq.refl true))
    (Eq.refl true))

noncomputable def p10400 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 1 32)
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p10386
        p10386)
      p10386))
  1

noncomputable def p10401 :=
@p10400 32 0 1 91 17179869184 1
  17179869184 91 549755813888 1 549755813888

noncomputable def p10402 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p10386
        p10386)
      p10386))
  false

noncomputable def p10403 :=
nat_lit 39157653052012698089288431257655569474245556270372262111624992448155050661573

noncomputable def p10404 :=
nat_lit 205688069665150755269371147819668813122841983204197482918576128000000

noncomputable def p10405 :=
@Enclosure.Real.IsNear.inv_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p10386
      p10386)
    p10386)
  p10403 p10404

noncomputable def p10406 :=
nat_lit 7049035653864953650076394977862833121540955377779568012791320646033871

noncomputable def p10407 :=
nat_lit 1153128668271417710668872213811552217475362137435209

noncomputable def p10408 :=
nat_lit 3484491437270409865864955980101306485309440000

noncomputable def p10409 :=
nat_lit 27677672044989006210293436906508628818193631

noncomputable def p10410 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p10386
    p10386)
  p10386 p10407 p10408 p10409

noncomputable def p10411 :=
@Enclosure.Real.IsNear.mulLit_ff p10386 p10386 p10394
  59029581035870565171200 81506205328590831 295147905179352825856000
  p10394 59029581035870565171200 81506205328590831
  295147905179352825856000 p10407

noncomputable def p10412 :=
@p10410 p5994 p10394 59029581035870565171200
  81506205328590831 295147905179352825856000 p10403 p10404
  p10406 p5990
  (@p10411 p10408 p10409 p5994
    p10397 p10397 (Eq.refl true))
  p10397

noncomputable def p10413 :=
@p10405 p10406 p5990 45 46
  8589934592 (p10412 (Eq.refl true)) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p10414 :=
p10401 (Enclosure.Real.IsNear.const false 1 32)
  (@p10402 91 17179869184 1 17179869184 91
    17179869184 1 17179869184 (p10413 (Eq.refl true))
    (Eq.refl true))

theorem d187 : p10385 201 549755813888 :=
@p10388 549755813888 201 549755813888
  (p10389 (Eq.refl true))
  (p10399 (p10414 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p10415 :=
@LE.le.{0} Real Real.instLE
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@OfNat.ofNat.{0} Real 32
      (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
    Real.pi)
  (@Prod.fst.{0, 0} Real Real (@NonemptyInterval.toProd.{0} Real Real.instLE d22))

noncomputable def p10416 :=
@OfNat.ofNat.{0} Real 506427
  (@instOfNatAtLeastTwo.{0} Real 506427
    (@AddMonoidWithOne.toNatCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real
            (@DivisionSemiring.toSemiring.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))))))
    (Mathlib.Meta.NormNum.instAtLeastTwo 506425))

noncomputable def p10417 :=
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
    p10416 p4068)

noncomputable def p10418 :=
@congrArg.{1, 1} Real Prop (@Prod.fst.{0, 0} Real Real (@NonemptyInterval.toProd.{0} Real Real.instLE d22))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real
    (@instHDiv.{0} Real
      (@DivInvMonoid.toDiv.{0} Real
        (@GroupWithZero.toDivInvMonoid.{0} Real
          (@DivisionSemiring.toGroupWithZero.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p10416 p4068)

noncomputable def p10419 :=
p10418
  (@LE.le.{0} Real Real.instLE
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 32
        (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
      Real.pi))

noncomputable def p10420 :=
@Mathlib.Meta.NormNum.IsNNRat.to_eq.{0} Real
  (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)) 506427 500
  (@Prod.fst.{0, 0} Real Real (@NonemptyInterval.toProd.{0} Real Real.instLE d22)) p10416
  p4068
  (@Mathlib.Meta.NormNum.isNNRat_ofScientific_of_true.{0} Real
    (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)) 101285400
    5 506427 500
    (p137
      (p138 p4
        (@p139 506427 500
          (p143 (@Eq.refl.{1} Nat (Nat.mul 101285400 1))
            (@Eq.refl.{1} Nat 100000))))))
  (@Eq.refl.{1} Real p10416)

noncomputable def p10421 :=
@congrArg.{1, 1} Real Prop
  (@HDiv.hDiv.{0, 0, 0} Real Real Real
    (@instHDiv.{0} Real
      (@DivInvMonoid.toDiv.{0} Real
        (@GroupWithZero.toDivInvMonoid.{0} Real
          (@DivisionSemiring.toGroupWithZero.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p10416 p4068)

noncomputable def p10422 :=
@p10421
  (@HDiv.hDiv.{0, 0, 0} Real Real Real
    (@instHDiv.{0} Real
      (@DivInvMonoid.toDiv.{0} Real
        (@GroupWithZero.toDivInvMonoid.{0} Real
          (@DivisionSemiring.toGroupWithZero.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p10416 p4068)

noncomputable def p10423 :=
p10422
  (@LE.le.{0} Real Real.instLE
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 32
        (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
      Real.pi))

noncomputable def p10424 :=
@Mathlib.Meta.NormNum.IsNNRat.to_eq.{0} Real
  (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)) 506427 500
  (@HDiv.hDiv.{0, 0, 0} Real Real Real
    (@instHDiv.{0} Real
      (@DivInvMonoid.toDiv.{0} Real
        (@GroupWithZero.toDivInvMonoid.{0} Real
          (@DivisionSemiring.toGroupWithZero.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p10416 p4068)

noncomputable def p10425 :=
@Mathlib.Meta.NormNum.isNNRat_mul.{0} Real
  (@DivisionSemiring.toSemiring.{0} Real
    (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real (@Distrib.toMul.{0} Real (@instDistribOfSemiring.{0} Real Real.semiring))))
  p10416
  (@Inv.inv.{0} Real
    (@InvOneClass.toInv.{0} Real
      (@DivInvOneMonoid.toInvOneClass.{0} Real
        (@DivisionMonoid.toDivInvOneMonoid.{0} Real
          (@GroupWithZero.toDivisionMonoid.{0} Real
            (@DivisionSemiring.toGroupWithZero.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))))))
    p4068)

noncomputable def p10426 :=
@p10425 506427 1 506427 1 500 500
  1
  (@Eq.refl.{1} (Real → Real → Real)
    (@HMul.hMul.{0, 0, 0} Real Real Real
      (@instHMul.{0} Real (@Distrib.toMul.{0} Real (@instDistribOfSemiring.{0} Real Real.semiring)))))
  (@Mathlib.Meta.NormNum.IsNat.to_isNNRat.{0} Real
    (@DivisionSemiring.toSemiring.{0} Real
      (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))
    p10416 506427
    (@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
      (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
      p10416 506427
      (@Eq.refl.{1} Real
        (@OfNat.ofNat.{0} Real 506427
          (@instOfNatAtLeastTwo.{0} Real 506427
            (@AddMonoidWithOne.toNatCast.{0} Real
              (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 506425))))))

noncomputable def p10427 :=
@p10424 p10416 p4068
  (@Mathlib.Meta.NormNum.isNNRat_div.{0} Real
    (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)) p10416
    p4068 506427 500
    (p10426 p4091 (@Eq.refl.{1} Nat (Nat.mul 506427 1))
      (@Eq.refl.{1} Nat 500)))
  (@Eq.refl.{1} Real p10416)

noncomputable def p10428 :=
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
    p10416 p4068)

noncomputable def p10429 :=
@LT.lt.{0} Real
  (@Preorder.toLT.{0} Real (@PartialOrder.toPreorder.{0} Real (@LinearOrder.toPartialOrder.{0} Real Real.linearOrder)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real
    (@instHDiv.{0} Real
      (@DivInvMonoid.toDiv.{0} Real
        (@GroupWithZero.toDivInvMonoid.{0} Real
          (@DivisionSemiring.toGroupWithZero.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p10416 p4068)

noncomputable def p10430 :=
@HMul.hMul.{0, 0, 0} Real Real Real
  (@instHMul.{0} Real (@Distrib.toMul.{0} Real (@instDistribOfSemiring.{0} Real Real.semiring)))
  (@OfNat.ofNat.{0} Real 456027
    (@instOfNatAtLeastTwo.{0} Real 456027
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))))
      (@Nat.instAtLeastTwoHAddOfNat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) 456025
          (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
        (@instNeZeroNatHAdd_1 456025 (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))

noncomputable def p10431 :=
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
  p10416

noncomputable def p10432 :=
@HSub.hSub.{0, 0, 0} Real Real Real
  (@instHSub.{0} Real
    (@SubNegMonoid.toSub.{0} Real
      (@AddGroup.toSubNegMonoid.{0} Real
        (@AddGroupWithOne.toAddGroup.{0} Real
          (@Ring.toAddGroupWithOne.{0} Real
            (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField)))))))
  p10431
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real
          (@DivisionSemiring.toSemiring.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p3705 (p8250 Real.pi))

noncomputable def p10433 :=
@HAdd.hAdd.{0, 0, 0} Real Real Real
  (@instHAdd.{0} Real (@AddSemigroup.toAdd.{0} Real (@AddMonoid.toAddSemigroup.{0} Real Real.instAddMonoid)))
  (p10430
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
  p10432

noncomputable def p10434 :=
@Eq.mp.{0}
  (@LT.lt.{0} Real (@Preorder.toLT.{0} Real (@PartialOrder.toPreorder.{0} Real Real.partialOrder))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real (@AddSemigroup.toAdd.{0} Real (@AddMonoid.toAddSemigroup.{0} Real Real.instAddMonoid)))
      p10433 (p8253 p3713))
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real (@MulZeroClass.toZero.{0} Real (@instMulZeroClassOfSemiring.{0} Real Real.semiring)))))
  (@LT.lt.{0} Real (@Preorder.toLT.{0} Real (@PartialOrder.toPreorder.{0} Real Real.partialOrder))
    (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real (@MulZeroClass.toZero.{0} Real (@instMulZeroClassOfSemiring.{0} Real Real.semiring)))))

noncomputable def p10435 :=
@Mathlib.Tactic.Ring.Common.add_congr.{0} Real Real.instCommSemiring p10433
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@Mathlib.Meta.NormNum.instAddMonoidWithOne.{0} Real
        (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)))
      50400)
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p8255
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))
  (p8253 p3713)

noncomputable def p10436 :=
@p10435
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 50400))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p8257
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))

noncomputable def p10437 :=
@Mathlib.Tactic.Ring.Common.add_congr.{0} Real Real.instCommSemiring
  (p10430
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
      (Int.negOfNat 456027))
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))

noncomputable def p10438 :=
@p10437 p10432
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      506427)
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p8255
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
      50400)
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p8255
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))

noncomputable def p10439 :=
@Mathlib.Tactic.Ring.Common.mul_congr.{0} Real Real.instCommSemiring
  (@OfNat.ofNat.{0} Real 456027
    (@instOfNatAtLeastTwo.{0} Real 456027
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))))
      (@Nat.instAtLeastTwoHAddOfNat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) 456025
          (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
        (@instNeZeroNatHAdd_1 456025 (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))

noncomputable def p10440 :=
@p10439
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      456027)
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

noncomputable def p10441 :=
@Mathlib.Tactic.Ring.cast_pos.{0} Real Real.instCommSemiring
  (@OfNat.ofNat.{0} Real 456027
    (@instOfNatAtLeastTwo.{0} Real 456027
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))))
      (@Nat.instAtLeastTwoHAddOfNat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) 456025
          (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
        (@instNeZeroNatHAdd_1 456025 (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))

noncomputable def p10442 :=
@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
  (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
  (@OfNat.ofNat.{0} Real 456027
    (@instOfNatAtLeastTwo.{0} Real 456027
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))))
      (@Nat.instAtLeastTwoHAddOfNat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) 456025
          (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
        (@instNeZeroNatHAdd_1 456025 (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))

noncomputable def p10443 :=
@p10440
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
      (Int.negOfNat 456027))
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@p10441 456027
    (@p10442 456027
      (@Eq.refl.{1} Real
        (@OfNat.ofNat.{0} Real 456027
          (@instOfNatAtLeastTwo.{0} Real 456027
            (@AddMonoidWithOne.toNatCast.{0} Real
              (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 456025))))))

noncomputable def p10444 :=
@Mathlib.Tactic.Ring.Common.add_mul.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    456027)
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
      (Int.negOfNat 456027))
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))

noncomputable def p10445 :=
@Mathlib.Tactic.Ring.Common.mul_add.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    456027)
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 1))
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 456027))

noncomputable def p10446 :=
@Mathlib.Meta.NormNum.IsInt.to_raw_eq.{0} Real
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      456027)
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 1)))
  (Int.negOfNat 456027)

noncomputable def p10447 :=
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
    456027)
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 1))

noncomputable def p10448 :=
@p10447 (Int.ofNat 456027) (Int.negOfNat 1) (Int.negOfNat 456027)
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
      456027)
    456027
    (@Mathlib.Meta.NormNum.IsNat.of_raw.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      456027))

noncomputable def p10449 :=
@p10445
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 456027))
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@p10446 (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (p10448
      (@Mathlib.Meta.NormNum.IsInt.of_raw.{0} Real
        (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)) (Int.negOfNat 1))
      (@Eq.refl.{1} Int (Int.negOfNat 456027))))
  (@Mathlib.Tactic.Ring.Common.mul_zero.{0} Real Real.instCommSemiring
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      456027))

noncomputable def p10450 :=
@p10444
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 456027))
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (p10449
    (@Mathlib.Tactic.Ring.Common.add_pf_add_zero.{0} Real Real.instCommSemiring
      (@HAdd.hAdd.{0, 0, 0} Real Real Real
        (@instHAdd.{0} Real
          (@Distrib.toAdd.{0} Real
            (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
        (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
          (Int.negOfNat 456027))
        (@OfNat.ofNat.{0} Real 0
          (@Zero.toOfNat0.{0} Real
            (@MulZeroClass.toZero.{0} Real
              (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))))

noncomputable def p10451 :=
p10450
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
        (Int.negOfNat 456027))
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))

noncomputable def p10452 :=
p10438
  (p10443
    (p3726 p3727
      (p3728
        (@Mathlib.Meta.NormNum.IsInt.to_raw_eq.{0} Real p3729 (Int.negOfNat 1)
          (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
          (p3733 (@Eq.refl.{1} Int (Int.negOfNat 1))))
        (@Mathlib.Tactic.Ring.Common.neg_zero.{0} Real Real.commRing)))
    p10451)

noncomputable def p10453 :=
@Mathlib.Tactic.Ring.Common.sub_congr.{0} Real Real.commRing p10431
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      506427)
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
    p3705 (p8250 Real.pi))

noncomputable def p10454 :=
@p3744 p10416
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      506427)
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
      506427)
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))

noncomputable def p10455 :=
p10454
  (p3746
    (p3747
      (@Nat.cast_one.{0} Real
        (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))))
  (@Mathlib.Tactic.Ring.cast_pos.{0} Real Real.instCommSemiring p10416 506427
    (@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
      (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
      p10416 506427
      (@Eq.refl.{1} Real
        (@OfNat.ofNat.{0} Real 506427
          (@instOfNatAtLeastTwo.{0} Real 506427
            (@AddMonoidWithOne.toNatCast.{0} Real
              (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 506425))))))

noncomputable def p10456 :=
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
      506427)
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
      506427)
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))

noncomputable def p10457 :=
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
    506427)
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    506427)

noncomputable def p10458 :=
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
      506427))
  506427

noncomputable def p10459 :=
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
    506427)
  1 506427

noncomputable def p10460 :=
@p10459 506427
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
    506427)
  (@Eq.refl.{1} Nat 506427)

noncomputable def p10461 :=
@p10457
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
      506427)
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@p10458
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p10460)

noncomputable def p10462 :=
p10461
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
        506427)
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))

noncomputable def p10463 :=
@p10456
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
      506427)
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  p10462

noncomputable def p10464 :=
p10463
  (@Mathlib.Tactic.Ring.Common.zero_mul.{0} Real Real.instCommSemiring
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      (@Nat.rawCast.{0} Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
            (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
        506427)
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))

noncomputable def p10465 :=
p10464
  (@Mathlib.Tactic.Ring.Common.add_pf_add_zero.{0} Real Real.instCommSemiring
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      (@Nat.rawCast.{0} Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
            (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
        506427)
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))

noncomputable def p10466 :=
@p10453
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p8257
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
      506427)
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p8255
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))
  (p10455 p10465)

noncomputable def p10467 :=
@Mathlib.Tactic.Ring.Common.sub_pf.{0} Real Real.commRing
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      506427)
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p8257
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))

noncomputable def p10468 :=
@p10467
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p8255
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
      506427)
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p8255
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))
  p8321

noncomputable def p10469 :=
@Mathlib.Tactic.Ring.Common.add_pf_add_lt.{0} Real Real.instCommSemiring
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p8255
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p8255
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    506427)

noncomputable def p10470 :=
p10468
  (p10469
    (@Mathlib.Tactic.Ring.Common.add_pf_zero_add.{0} Real Real.instCommSemiring
      (@HAdd.hAdd.{0, 0, 0} Real Real Real
        (@instHAdd.{0} Real
          (@Distrib.toAdd.{0} Real
            (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
        p8255
        (@OfNat.ofNat.{0} Real 0
          (@Zero.toOfNat0.{0} Real
            (@MulZeroClass.toZero.{0} Real
              (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))))

noncomputable def p10471 :=
@Mathlib.Tactic.Ring.Common.add_pf_add_overlap.{0} Real Real.instCommSemiring
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 456027))
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    506427)
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p8255
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@Nat.rawCast.{0} Real
    (@Mathlib.Meta.NormNum.instAddMonoidWithOne.{0} Real
      (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)))
    50400)
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p8255
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))

noncomputable def p10472 :=
@Mathlib.Meta.NormNum.IsNat.to_raw_eq.{0} Real
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 456027))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      506427))
  50400
  (@Mathlib.Meta.NormNum.instAddMonoidWithOne.{0} Real
    (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)))

noncomputable def p10473 :=
@Mathlib.Meta.NormNum.isInt_add.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 456027))
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    506427)
  (Int.negOfNat 456027) (Int.ofNat 506427)

noncomputable def p10474 :=
@p10473 (Int.ofNat 50400)
  (@Eq.refl.{1} (Real → Real → Real)
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@Mathlib.Meta.NormNum.IsInt.of_raw.{0} Real
    (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)) (Int.negOfNat 456027))
  (@Mathlib.Meta.NormNum.IsNat.to_isInt.{0} Real
    (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      506427)
    506427
    (@Mathlib.Meta.NormNum.IsNat.of_raw.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      506427))

noncomputable def p10475 :=
@Mathlib.Meta.NormNum.IsInt.to_isNat.{0} Real
  (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 456027))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      506427))
  50400 (p10474 (@Eq.refl.{1} Int (Int.ofNat 50400)))

noncomputable def p10476 :=
p10452
  (p10466
    (p8291 (p8297 p8306) p8315)
    p10470)
  (p10471 (p10472 p10475)
    (@Mathlib.Tactic.Ring.Common.add_pf_zero_add.{0} Real Real.instCommSemiring
      (@HAdd.hAdd.{0, 0, 0} Real Real Real
        (@instHAdd.{0} Real
          (@Distrib.toAdd.{0} Real
            (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
        p8255
        (@OfNat.ofNat.{0} Real 0
          (@Zero.toOfNat0.{0} Real
            (@MulZeroClass.toZero.{0} Real
              (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))))

noncomputable def p10477 :=
@Mathlib.Tactic.Ring.of_eq.{1} Real
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real (@AddSemigroup.toAdd.{0} Real (@AddMonoid.toAddSemigroup.{0} Real Real.instAddMonoid)))
    p10433 (p8253 p3713))
  (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (p10436 p10476
    (p8336
      (p3840 (p3842 p3852) p3860)
      p8354)
    (@p8355
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
      p8358
      (p8363
        (@Mathlib.Tactic.Ring.Common.add_pf_zero_add.{0} Real Real.instCommSemiring
          (@OfNat.ofNat.{0} Real 0
            (@Zero.toOfNat0.{0} Real
              (@MulZeroClass.toZero.{0} Real
                (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))))

noncomputable def p10478 :=
@congrArg.{1, 1} Real Prop
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real (@AddSemigroup.toAdd.{0} Real (@AddMonoid.toAddSemigroup.{0} Real Real.instAddMonoid)))
    p10433 (p8253 p3713))
  (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
  (fun (_a : Real) =>
    @LT.lt.{0} Real (@Preorder.toLT.{0} Real (@PartialOrder.toPreorder.{0} Real Real.partialOrder)) _a
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real (@MulZeroClass.toZero.{0} Real (@instMulZeroClassOfSemiring.{0} Real Real.semiring)))))
  (p10477
    (@Mathlib.Tactic.Ring.cast_zero.{0} Real Real.instCommSemiring
      (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
      (@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
        (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
        (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) 0
        (@Nat.cast_zero.{0} Real
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))))))

noncomputable def p10479 :=
@HAdd.hAdd.{0, 0, 0} Real Real Real
  (@instHAdd.{0} Real (@Distrib.toAdd.{0} Real (@instDistribOfSemiring.{0} Real Real.semiring)))
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real (@instDistribOfSemiring.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))))
    (@OfNat.ofNat.{0} Real 456027
      (@instOfNatAtLeastTwo.{0} Real 456027 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 456026 (instOfNatNat 456026))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 456025 (instOfNatNat 456025))))))
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
  p10432

noncomputable def p10480 :=
@Mathlib.Tactic.Linarith.add_neg.{0} Real Real.semiring Real.partialOrder Real.instIsStrictOrderedRing
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real (@instDistribOfSemiring.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))))
    (@OfNat.ofNat.{0} Real 456027
      (@instOfNatAtLeastTwo.{0} Real 456027 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 456026 (instOfNatNat 456026))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 456025 (instOfNatNat 456025))))))
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
  p10432

noncomputable def p10481 :=
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
  (@OfNat.ofNat.{0} Real 456027
    (@instOfNatAtLeastTwo.{0} Real 456027 Real.instNatCast
      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 456026 (instOfNatNat 456026))
        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 456025 (instOfNatNat 456025))))))
  (@neg_neg_of_pos.{0} Real Real.instAddCommGroup Real.partialOrder Real.instIsOrderedAddMonoid
    (@OfNat.ofNat.{0} Real 1
      (@One.toOfNat1.{0} Real
        (@AddMonoidWithOne.toOne.{0} Real
          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
            (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
              (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))))))
    (@Mathlib.Tactic.Linarith.zero_lt_one.{0} Real Real.semiring Real.partialOrder Real.instIsStrictOrderedRing))

noncomputable def p10482 :=
@Mathlib.Meta.NormNum.isNat_lt_true.{0} Real Real.semiring Real.partialOrder Real.instIsOrderedRing
  (@FloorSemiring.instCharZero.{0} Real (@Ring.toSemiring.{0} Real Real.instRing) Real.partialOrder
    (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing))
  (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
  (@OfNat.ofNat.{0} Real 456027
    (@instOfNatAtLeastTwo.{0} Real 456027 Real.instNatCast
      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 456026 (instOfNatNat 456026))
        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 456025 (instOfNatNat 456025))))))
  0 456027
  (@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
    (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
    (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) 0
    (@Nat.cast_zero.{0} Real
      (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))))

noncomputable def p10483 :=
p10482
  (@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
    (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
    (@OfNat.ofNat.{0} Real 456027
      (@instOfNatAtLeastTwo.{0} Real 456027 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 456026 (instOfNatNat 456026))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 456025 (instOfNatNat 456025))))))
    456027
    (@Eq.refl.{1} Real
      (@OfNat.ofNat.{0} Real 456027
        (@instOfNatAtLeastTwo.{0} Real 456027
          (@AddMonoidWithOne.toNatCast.{0} Real
            (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
          (Mathlib.Meta.NormNum.instAtLeastTwo 456025)))))

noncomputable def p10484 :=
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
    p10416 p4068)

noncomputable def p10485 :=
p8371
  (p10484
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 32
        (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
      Real.pi))

noncomputable def p10486 :=
@Mathlib.Tactic.CancelDenoms.derive_trans.{0} Real Real.instMul
  (p10484
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 32
        (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
      Real.pi))

noncomputable def p10487 :=
@p10486
  (p10484
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 32
        (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
      Real.pi))

noncomputable def p10488 :=
@p10487
  (@OfNat.ofNat.{0} Real 500
    (@instOfNatAtLeastTwo.{0} Real 500
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p10489 :=
@congrArg.{1, 1} Real (Real → Real)
  (@HDiv.hDiv.{0, 0, 0} Real Real Real
    (@instHDiv.{0} Real
      (@DivInvMonoid.toDiv.{0} Real
        (@GroupWithZero.toDivInvMonoid.{0} Real
          (@DivisionSemiring.toGroupWithZero.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p10416 p4068)

noncomputable def p10490 :=
@p10489
  (@HDiv.hDiv.{0, 0, 0} Real Real Real
    (@instHDiv.{0} Real
      (@DivInvMonoid.toDiv.{0} Real
        (@GroupWithZero.toDivInvMonoid.{0} Real
          (@DivisionSemiring.toGroupWithZero.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p10416 p4068)

noncomputable def p10491 :=
@congrFun'.{1, 1} Real Real p10484 p10484
  (p10490
    (@HSub.hSub.{0, 0, 0} Real Real Real
      (@instHSub.{0} Real
        (@SubNegMonoid.toSub.{0} Real
          (@AddGroup.toSubNegMonoid.{0} Real
            (@AddGroupWithOne.toAddGroup.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))))))
    (p10427 (@Eq.refl.{1} Real p4068)))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@OfNat.ofNat.{0} Real 32
      (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
    Real.pi)

noncomputable def p10492 :=
@p8380
  (@HDiv.hDiv.{0, 0, 0} Real Real Real
    (@instHDiv.{0} Real
      (@DivInvMonoid.toDiv.{0} Real
        (@GroupWithZero.toDivInvMonoid.{0} Real
          (@DivisionSemiring.toGroupWithZero.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p10416 p4068)

noncomputable def p10493 :=
@p10492
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@OfNat.ofNat.{0} Real 32
      (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
    Real.pi)
  p10431

noncomputable def p10494 :=
@p10493
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real
          (@DivisionSemiring.toSemiring.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p3705 (p8250 Real.pi))

noncomputable def p10495 :=
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
  p10416

noncomputable def p10496 :=
@p8385 p10416 p4068 p10431
  (@rfl.{1} Real p10495)
  (p8388 p8397
    (p3747
      (@Nat.cast_one.{0} Real
        (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))))
  (@p8399 500 p8401
    (@p8295 500
      (@Eq.refl.{1} Real
        (@OfNat.ofNat.{0} Real 500
          (@instOfNatAtLeastTwo.{0} Real 500
            (@AddMonoidWithOne.toNatCast.{0} Real
              (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 498))))))

noncomputable def p10497 :=
@Eq.mp.{0}
  (@LT.lt.{0} Real (@Preorder.toLT.{0} Real (@PartialOrder.toPreorder.{0} Real Real.partialOrder))
    p10485
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))))))
  (@LT.lt.{0} Real (@Preorder.toLT.{0} Real (@PartialOrder.toPreorder.{0} Real Real.partialOrder))
    p10432
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))))))
  (@congrArg.{1, 1} Real Prop p10485 p10432
    (fun (_a : Real) =>
      @LT.lt.{0} Real (@Preorder.toLT.{0} Real (@PartialOrder.toPreorder.{0} Real Real.partialOrder)) _a
        (@OfNat.ofNat.{0} Real 0
          (@Zero.toOfNat0.{0} Real
            (@MulZeroClass.toZero.{0} Real
              (@instMulZeroClassOfSemiring.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))))))
    (@p10488 p10432 p10491
      (p10494 p10496 p8407)))

noncomputable def p10498 :=
@Mathlib.Tactic.Linarith.mul_neg.{0} Real Real.instRing Real.partialOrder Real.instIsStrictOrderedRing
  (p10484
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 32
        (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
      Real.pi))

noncomputable def p10499 :=
@Mathlib.Tactic.Linarith.sub_neg_of_lt.{0} Real Real.instRing Real.partialOrder Real.instIsOrderedRing
  (@HDiv.hDiv.{0, 0, 0} Real Real Real
    (@instHDiv.{0} Real
      (@DivInvMonoid.toDiv.{0} Real
        (@GroupWithZero.toDivInvMonoid.{0} Real
          (@DivisionSemiring.toGroupWithZero.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p10416 p4068)

noncomputable def p10500 :=
fun
    (a :
      p10429
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real 32
            (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
          Real.pi)) =>
  @Mathlib.Tactic.Linarith.lt_irrefl.{0} Real Real.instPreorder
    (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
    (p10434 p10478
      (@Mathlib.Tactic.Linarith.add_neg.{0} Real Real.semiring Real.partialOrder Real.instIsStrictOrderedRing
        p10479
        (@HMul.hMul.{0, 0, 0} Real Real Real
          (@instHMul.{0} Real
            (@Distrib.toMul.{0} Real (@instDistribOfSemiring.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))))
          (@OfNat.ofNat.{0} Real 800
            (@instOfNatAtLeastTwo.{0} Real 800 Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 799 (instOfNatNat 799))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 798 (instOfNatNat 798))))))
          p3713)
        (p10480 (p10481 (p10483 (@Eq.refl.{1} Bool false)))
          (p10497
            (@p10498
              (@OfNat.ofNat.{0} Real 500
                (@instOfNatAtLeastTwo.{0} Real 500 Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 499 (instOfNatNat 499))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 498 (instOfNatNat 498))))))
              (@p10499
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real 32
                    (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
                  Real.pi)
                a)
              (p8412 (@Eq.refl.{1} Bool false)))))
        (@Mathlib.Tactic.Linarith.mul_neg.{0} Real Real.instRing Real.partialOrder Real.instIsStrictOrderedRing
          p3713
          (@OfNat.ofNat.{0} Real 800
            (@instOfNatAtLeastTwo.{0} Real 800 Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 799 (instOfNatNat 799))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 798 (instOfNatNat 798))))))
          p3995 (p8414 (@Eq.refl.{1} Bool false)))))

noncomputable def p10501 :=
@Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal d22)
  (hardyZApproximantRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
      true 5))
  false p9181 p9182

noncomputable def p10502 :=
@Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.fstVal d22) p9181
  p9182 p9184 p9185
  (@p10501 p9184 p9185
    (@Eq.refl.{1} Real
      (hardyZApproximantRS
        (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
          true 5)))
    d184)

noncomputable def p10503 :=
@Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal d22)
  (hardyZApproximantRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
      true 5))
  true p9768 p9769

noncomputable def p10504 :=
@Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.sndVal d22) p9768
  p9769 p9771 p9772
  (@p10503 p9771 p9772
    (@Eq.refl.{1} Real
      (hardyZApproximantRS
        (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
          true 5)))
    d185)

noncomputable def p10505 :=
@Zeta.Certificates.ZIntervalRS.Certificate.mk d22
  (@Eq.mpr.{0} p10415 p10417
    (@id.{0} (@Eq.{1} Prop p10415 p10417)
      (@Eq.trans.{1} Prop p10415 p10417 p10417
        (p10419 (p10420 (@Eq.refl.{1} Real p4068)))
        (p10423 (p10427 (@Eq.refl.{1} Real p4068)))))
    (p10428 p10500))
  (BSN.mul_neg_of_pos_neg_r (Zeta.Certificates.ZIntervalRS.fstVal d22)
    (Zeta.Certificates.ZIntervalRS.sndVal d22)
    (p10502 (Eq.refl true) (Eq.refl true) (Eq.refl true))
    (p10504 (Eq.refl true) (Eq.refl true)
      (Eq.refl true)))

noncomputable def p10506 :=
@Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal d22)
  (hardyZErrorBoundRS (@Prod.fst.{0, 0} Real Real (@NonemptyInterval.toProd.{0} Real Real.instLE d22)))
  false false p9181 p9182 p9184

noncomputable def p10507 :=
@p10506 p9185 5981927491 549755813888 201
  549755813888
  (@p10501 p9184 p9185
    (@Eq.refl.{1} Real
      (hardyZApproximantRS
        (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
          true 5)))
    d184)

noncomputable def p10508 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZErrorBoundRS (@Prod.fst.{0, 0} Real Real (@NonemptyInterval.toProd.{0} Real Real.instLE d22)))
  (hardyZErrorBoundRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
      true 5))
  false 5981927491 549755813888

noncomputable def p10509 :=
p10507
  (@p10508 201 549755813888
    (@Eq.refl.{1} Real
      (hardyZErrorBoundRS
        (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101285400
          true 5)))
    d186)

noncomputable def p10510 :=
@Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal d22)
  (hardyZErrorBoundRS (@Prod.snd.{0, 0} Real Real (@NonemptyInterval.toProd.{0} Real Real.instLE d22)))
  true false p9768 p9769 p9771

noncomputable def p10511 :=
@p10510 p9772 5972837091 549755813888 201
  549755813888
  (@p10503 p9771 p9772
    (@Eq.refl.{1} Real
      (hardyZApproximantRS
        (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
          true 5)))
    d185)

noncomputable def p10512 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZErrorBoundRS (@Prod.snd.{0, 0} Real Real (@NonemptyInterval.toProd.{0} Real Real.instLE d22)))
  (hardyZErrorBoundRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
      true 5))
  false 5972837091 549755813888

noncomputable def p10513 :=
p10511
  (@p10512 201 549755813888
    (@Eq.refl.{1} Real
      (hardyZErrorBoundRS
        (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101408700
          true 5)))
    d187)

theorem d188 : Zeta.Certificates.ZIntervalRS.Certificate d22 :=
p10505
  (p10509 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (p10513 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
end RHHeight1000.GramZero658

theorem solution : ∃ t ∈ Set.Ioo (1012.85400 : ℝ) (1014.08700 : ℝ), riemannZeta (1 / 2 + Complex.I * t) = 0 := by
  exact riemannZeta.exists_zero_of_zIntervalRS_certificate _ RHHeight1000.GramZero658.d188
