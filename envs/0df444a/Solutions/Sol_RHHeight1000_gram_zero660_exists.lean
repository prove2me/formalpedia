-- Prove2me | solution 1 for RHHeight1000.gram_zero660_exists
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-19T16:54:36.071974+00:00
-- url     : https://prove2.me/submissions/9ca1baf3-c9df-4cb3-9790-7441b37bc196

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

namespace RHHeight1000.GramZero660
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

noncomputable abbrev c14 := (@OfNat.ofNat Real 457263
    (@instOfNatAtLeastTwo Real 457263
      (@AddMonoidWithOne.toNatCast Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne Real
          (@NonAssocSemiring.toAddCommMonoidWithOne Real (@Semiring.toNonAssocSemiring Real Real.semiring))))
      (@Nat.instAtLeastTwoHAddOfNat
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) 457261
          (@OfNat.ofNat Nat 1 (instOfNatNat 1)))
        (@instNeZeroNatHAdd_1 457261 (@OfNat.ofNat Nat 1 (instOfNatNat 1))
          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 0 (instOfNatNat 0)))))))

noncomputable abbrev c15 := (@OfNat.ofNat Real 800
    (@instOfNatAtLeastTwo Real 800
      (@AddMonoidWithOne.toNatCast Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne Real
          (@NonAssocSemiring.toAddCommMonoidWithOne Real (@Semiring.toNonAssocSemiring Real Real.semiring))))
      (@Nat.instAtLeastTwoHAddOfNat
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) 798
          (@OfNat.ofNat Nat 1 (instOfNatNat 1)))
        (@instNeZeroNatHAdd_1 798 (@OfNat.ofNat Nat 1 (instOfNatNat 1))
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

noncomputable abbrev c30 := (@OfNat.ofNat Real 457263
      (@instOfNatAtLeastTwo Real 457263 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 457262 (instOfNatNat 457262))
          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 457261 (instOfNatNat 457261))))))

noncomputable abbrev c31 := (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@Ring.toSemiring Real Real.instRing)))))

noncomputable abbrev c32 := (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))

noncomputable abbrev c33 := (@instHSub Real
      (@SubNegMonoid.toSub Real
        (@AddGroup.toSubNegMonoid Real
          (@AddGroupWithOne.toAddGroup Real (@Ring.toAddGroupWithOne Real Real.instRing)))))

noncomputable abbrev c34 := (@Semiring.toNonAssocSemiring Nat (@CommSemiring.toSemiring Nat Nat.instCommSemiring))

noncomputable abbrev c35 := (@Nat.cast Real Real.instNatCast 70368744177664)

noncomputable abbrev c36 := (@instHAdd Real (@AddSemigroup.toAdd Real (@AddMonoid.toAddSemigroup Real Real.instAddMonoid)))

noncomputable abbrev c37 := (@NegZeroClass.toNeg Real
      (@SubNegZeroMonoid.toNegZeroClass Real
        (@SubtractionMonoid.toSubNegZeroMonoid Real
          (@SubtractionCommMonoid.toSubtractionMonoid Real
            (@AddCommGroup.toDivisionAddCommMonoid Real Real.instAddCommGroup)))))

noncomputable abbrev c38 := (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))

noncomputable abbrev c39 := (@OfNat.ofNat Real 800
            (@instOfNatAtLeastTwo Real 800 Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 799 (instOfNatNat 799))
                (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 798 (instOfNatNat 798))))))

noncomputable abbrev c40 := (@OfNat.ofNat Real 1
    (@One.toOfNat1 Real
      (@AddMonoidWithOne.toOne Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne Real
          (@NonAssocSemiring.toAddCommMonoidWithOne Real (@Semiring.toNonAssocSemiring Real Real.semiring))))))

noncomputable abbrev c41 := (@OfNat.ofNat Real 457263
    (@instOfNatAtLeastTwo Real 457263 Real.instNatCast
      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 457262 (instOfNatNat 457262))
        (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 457261 (instOfNatNat 457261))))))

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

noncomputable abbrev c59 := (@Nat.cast Real Real.instNatCast 314789802202079)

noncomputable abbrev c60 := (@Nat.cast Real Real.instNatCast 39774839490359)

noncomputable abbrev c61 := (@Nat.cast Real Real.instNatCast 8796093022208)

noncomputable abbrev c62 := (@instHDiv Real
    (@DivInvMonoid.toDiv Real
      (@DivisionRing.toDivInvMonoid Real (@Field.toDivisionRing Real Real.instField))))

noncomputable abbrev c63 := (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 498 (instOfNatNat 498)))

noncomputable abbrev c64 := (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 30 (instOfNatNat 30)))

noncomputable abbrev c65 := (@Mathlib.Tactic.Ring.Common.neg_zero Real Real.commRing)

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

noncomputable def p218 :=
@Mathlib.Meta.NormNum.isRat_le_true Real
  c32 Real.linearOrder
  Real.instIsStrictOrderedRing
  (@OfScientific.ofScientific Real c2 101532600
    true 5)
  (@OfScientific.ofScientific Real c2 101655800
    true 5)
  (Int.ofNat 507663) (Int.ofNat 508279) 500

noncomputable def p219 :=
@Mathlib.Meta.NormNum.isNNRat_nnratCast Real
  c3
  (@FloorSemiring.instCharZero Real Real.semiring Real.partialOrder
    c26)
  (NNRat.divNat 101532600
    (@HPow.hPow Nat Nat Nat
      c27
      (@OfNat.ofNat Nat 10 (instOfNatNat 10)) 5))
  507663 500

noncomputable def p220 :=
@Mathlib.Meta.NormNum.isNNRat_divNat 101532600 101532600 507663
  (@HPow.hPow Nat Nat Nat
    c27
    (@OfNat.ofNat Nat 10 (instOfNatNat 10)) 5)
  100000 500 (Mathlib.Meta.NormNum.IsNat.raw_refl 101532600)

noncomputable def p221 :=
@Mathlib.Meta.NormNum.isNNRat_div NNRat c47
  (@Nat.cast NNRat
    c6
    101532600)
  (@Nat.cast NNRat
    c6
    100000)

noncomputable def p222 :=
@Mathlib.Meta.NormNum.isNNRat_mul NNRat
  c12
  (@HMul.hMul NNRat NNRat NNRat
    (@instHMul NNRat
      (@Distrib.toMul NNRat
        (@instDistribOfSemiring NNRat
          c12))))
  (@Nat.cast NNRat
    c6
    101532600)
  (@Inv.inv NNRat
    c28
    (@Nat.cast NNRat
      (@AddMonoidWithOne.toNatCast NNRat
        (@AddCommMonoidWithOne.toAddMonoidWithOne NNRat
          (@NonAssocSemiring.toAddCommMonoidWithOne NNRat
            (@Semiring.toNonAssocSemiring NNRat
              c12))))
      100000))

noncomputable def p223 :=
@Mathlib.Meta.NormNum.IsNat.to_isNNRat NNRat
  c12
  (@Nat.cast NNRat
    c6
    101532600)
  101532600

noncomputable def p224 :=
p223
  (@Mathlib.Meta.NormNum.isNat_natCast NNRat
    (@AddCommMonoidWithOne.toAddMonoidWithOne NNRat
      (@NonAssocSemiring.toAddCommMonoidWithOne NNRat
        (@Semiring.toNonAssocSemiring NNRat
          c12)))
    101532600 101532600 (Mathlib.Meta.NormNum.IsNat.raw_refl 101532600))

noncomputable def p225 :=
@p222 101532600 1 507663 1 100000 500
  200
  (@Eq.refl (NNRat → NNRat → NNRat)
    (@HMul.hMul NNRat NNRat NNRat
      (@instHMul NNRat
        (@Distrib.toMul NNRat
          (@instDistribOfSemiring NNRat
            c12)))))
  p224 (@p9 1 p11)

noncomputable def p226 :=
@p218 500
  (@Mathlib.Meta.NormNum.IsNNRat.to_isRat Real
    c32
    (@OfScientific.ofScientific Real c2 101532600
      true 5)
    507663 500
    (@Mathlib.Meta.NormNum.isNNRat_ofScientific_of_true Real
      c3 101532600
      5 507663 500
      (p219
        (p220 p4
          (@p221 507663 500
            (p225 (@Eq.refl Nat (Nat.mul 101532600 1))
              (@Eq.refl Nat 100000)))))))

noncomputable def p227 :=
@Mathlib.Meta.NormNum.isNNRat_nnratCast Real
  c3
  (@FloorSemiring.instCharZero Real Real.semiring Real.partialOrder
    c26)
  (NNRat.divNat 101655800
    (@HPow.hPow Nat Nat Nat
      c27
      (@OfNat.ofNat Nat 10 (instOfNatNat 10)) 5))
  508279 500

noncomputable def p228 :=
@Mathlib.Meta.NormNum.isNNRat_divNat 101655800 101655800 508279
  (@HPow.hPow Nat Nat Nat
    c27
    (@OfNat.ofNat Nat 10 (instOfNatNat 10)) 5)
  100000 500 (Mathlib.Meta.NormNum.IsNat.raw_refl 101655800)

noncomputable def p229 :=
@Mathlib.Meta.NormNum.isNNRat_div NNRat c47
  (@Nat.cast NNRat
    c6
    101655800)
  (@Nat.cast NNRat
    c6
    100000)

noncomputable def p230 :=
@Mathlib.Meta.NormNum.isNNRat_mul NNRat
  c12
  (@HMul.hMul NNRat NNRat NNRat
    (@instHMul NNRat
      (@Distrib.toMul NNRat
        (@instDistribOfSemiring NNRat
          c12))))
  (@Nat.cast NNRat
    c6
    101655800)
  (@Inv.inv NNRat
    c28
    (@Nat.cast NNRat
      (@AddMonoidWithOne.toNatCast NNRat
        (@AddCommMonoidWithOne.toAddMonoidWithOne NNRat
          (@NonAssocSemiring.toAddCommMonoidWithOne NNRat
            (@Semiring.toNonAssocSemiring NNRat
              c12))))
      100000))

noncomputable def p231 :=
@Mathlib.Meta.NormNum.IsNat.to_isNNRat NNRat
  c12
  (@Nat.cast NNRat
    c6
    101655800)
  101655800

noncomputable def p232 :=
p231
  (@Mathlib.Meta.NormNum.isNat_natCast NNRat
    (@AddCommMonoidWithOne.toAddMonoidWithOne NNRat
      (@NonAssocSemiring.toAddCommMonoidWithOne NNRat
        (@Semiring.toNonAssocSemiring NNRat
          c12)))
    101655800 101655800 (Mathlib.Meta.NormNum.IsNat.raw_refl 101655800))

noncomputable def p233 :=
@p230 101655800 1 508279 1 100000 500
  200
  (@Eq.refl (NNRat → NNRat → NNRat)
    (@HMul.hMul NNRat NNRat NNRat
      (@instHMul NNRat
        (@Distrib.toMul NNRat
          (@instDistribOfSemiring NNRat
            c12)))))
  p232 (@p9 1 p11)

noncomputable def p234 :=
p226
  (@Mathlib.Meta.NormNum.IsNNRat.to_isRat Real
    c32
    (@OfScientific.ofScientific Real c2 101655800
      true 5)
    508279 500
    (@Mathlib.Meta.NormNum.isNNRat_ofScientific_of_true Real
      c3 101655800
      5 508279 500
      (p227
        (p228 p4
          (@p229 508279 500
            (p233 (@Eq.refl Nat (Nat.mul 101655800 1))
              (@Eq.refl Nat 100000)))))))

theorem d35 : @LE.le Real
  (@Preorder.toLE Real
    (@PartialOrder.toPreorder Real
      (@SemilatticeInf.toPartialOrder Real
        (@Lattice.toSemilatticeInf Real
          (@DistribLattice.toLattice Real (@instDistribLatticeOfLinearOrder Real Real.linearOrder))))))
  (@OfScientific.ofScientific Real c2 101532600
    true 5)
  (@OfScientific.ofScientific Real c2 101655800
    true 5) :=
p234 (Eq.refl true)

noncomputable def d36 :=
@NonemptyInterval.mk Real Real.instLE
  (@Prod.mk Real Real
    (@OfScientific.ofScientific Real c2 101532600
      true 5)
    (@OfScientific.ofScientific Real c2 101655800
      true 5))
  d35

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

noncomputable def p2314 :=
Enclosure.Real.IsNear
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 4 1) Real.pi)
  false 884279719003555 70368744177664 1

noncomputable def p2315 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 4 1) Real.pi 4 1
  0 1 226375608064910080 72057594037927936

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

noncomputable def p2658 :=
nat_lit
  104748499452676539840422070298483172870932545473378073263465323779076281484949585756264642954428933028828373892081922272294952209468332577706512882860032

noncomputable def p2977 :=
nat_lit 6129982163463555433433388108601236734474956488734408704

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

noncomputable def p3667 :=
nat_lit 3213876088517980551083924184682325205044405987565585670602752000000000

noncomputable def p3671 :=
nat_lit 21778071482940061661655974875633165533184000000

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
          c64)))
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
              c34))
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
            c34))
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
    c65)

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
    c33
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
    c33
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
  c62
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
    c33
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

noncomputable def p4068 :=
@OfNat.ofNat Real 500
  (@instOfNatAtLeastTwo Real 500
    (@AddMonoidWithOne.toNatCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real
            (@DivisionSemiring.toSemiring Real
              c3)))))
    (Mathlib.Meta.NormNum.instAtLeastTwo 498))

noncomputable def p4091 :=
@Mathlib.Meta.NormNum.isNNRat_inv_pos Real
  c3
  (@FloorSemiring.instCharZero Real Real.semiring Real.partialOrder
    c26)
  p4068 499 1
  (@Mathlib.Meta.NormNum.IsNat.to_isNNRat Real
    (@DivisionSemiring.toSemiring Real
      c3)
    p4068 500
    (@Mathlib.Meta.NormNum.isNat_ofNat Real
      c5
      p4068 500
      (@Eq.refl Real
        (@OfNat.ofNat Real 500
          (@instOfNatAtLeastTwo Real 500
            (@AddMonoidWithOne.toNatCast Real
              c5)
            (Mathlib.Meta.NormNum.instAtLeastTwo 498))))))

noncomputable def p4996 :=
nat_lit 951160241300648755200000000

noncomputable def p5018 :=
nat_lit 73786976294838206464000000000000000

noncomputable def p7870 :=
nat_lit
  280528748176849183015425539339920495498509234119743350333152695834048405533944936582523226145133583973145537760862060363055975506138532699271526653087437574266421248000

noncomputable def p7873 :=
nat_lit
  42920898471057925001360107519007835811271912820320732600972362462609406046693575297126053600205438347891267277411895235547564252439195502988543577922377948862762450944000

noncomputable def p8159 :=
nat_lit 12259964326927110866866776217202473468949912977468817408

noncomputable def p8250 :=
@HMul.hMul Real Real Real
  (@instHMul Real
    (@Distrib.toMul Real
      (@instDistribOfSemiring Real
        (@DivisionSemiring.toSemiring Real
          c3))))
  (@OfNat.ofNat Real 500
    (@instOfNatAtLeastTwo Real 500
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8253 :=
@HMul.hMul Real Real Real
  c19
  c15

noncomputable def p8255 :=
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
    (Int.negOfNat 16000))

noncomputable def p8257 :=
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
    16000)

noncomputable def p8289 :=
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
  (p8250 Real.pi)

noncomputable def p8290 :=
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
    500)

noncomputable def p8291 :=
@p8289
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p8290
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p8257
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

noncomputable def p8292 :=
@Mathlib.Tactic.Ring.Common.mul_congr Real Real.instCommSemiring
  (@OfNat.ofNat Real 500
    (@instOfNatAtLeastTwo Real 500
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8293 :=
@p8292
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      500)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  Real.pi

noncomputable def p8294 :=
@Mathlib.Tactic.Ring.cast_pos Real Real.instCommSemiring
  (@OfNat.ofNat Real 500
    (@instOfNatAtLeastTwo Real 500
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8295 :=
@Mathlib.Meta.NormNum.isNat_ofNat Real
  c5
  (@OfNat.ofNat Real 500
    (@instOfNatAtLeastTwo Real 500
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8296 :=
@p8293
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
    p8290
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@p8294 500
    (@p8295 500
      (@Eq.refl Real
        (@OfNat.ofNat Real 500
          (@instOfNatAtLeastTwo Real 500
            (@AddMonoidWithOne.toNatCast Real
              c5)
            (Mathlib.Meta.NormNum.instAtLeastTwo 498))))))

noncomputable def p8297 :=
p8296
  (@Mathlib.Tactic.Ring.Common.atom_pf Real Real.instCommSemiring p3777 Real.pi
    c9
    (@rfl Nat
      (@Nat.rawCast Nat
        (@AddCommMonoidWithOne.toAddMonoidWithOne Nat
          (@NonAssocSemiring.toAddCommMonoidWithOne Nat
            c34))
        1))
    (@Eq.mpr (@Eq Real p3777 p3777)
      (@Eq Real p3777 p3777)
      (@id
        (@Eq Prop (@Eq Real p3777 p3777)
          (@Eq Real p3777 p3777))
        p3782)
      (@Eq.refl Real p3777)))

noncomputable def p8298 :=
@Mathlib.Tactic.Ring.Common.add_mul Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    500)
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
    p8290
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))

noncomputable def p8299 :=
@Mathlib.Tactic.Ring.Common.mul_add Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    500)
  p3777
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  p8290

noncomputable def p8300 :=
@Mathlib.Tactic.Ring.Common.mul_pf_right Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    500)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    500)
  Real.pi

noncomputable def p8301 :=
@Mathlib.Meta.NormNum.IsNat.to_raw_eq Real
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      500)
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      1))
  500

noncomputable def p8302 :=
@Mathlib.Meta.NormNum.isNat_mul Real c0
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real c0))))
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    500)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1)
  500 1

noncomputable def p8303 :=
@p8302 500
  (@Eq.refl (Real → Real → Real)
    (@HMul.hMul Real Real Real
      (@instHMul Real
        (@Distrib.toMul Real
          (@instDistribOfSemiring Real c0)))))
  (@Mathlib.Meta.NormNum.IsNat.of_raw Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    500)
  (@Mathlib.Meta.NormNum.IsNat.of_raw Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1)
  (@Eq.refl Nat 500)

noncomputable def p8304 :=
@p8299
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p8290
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (p8300
    c9
    (@p8301
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      p8303))
  (@Mathlib.Tactic.Ring.Common.mul_zero Real Real.instCommSemiring
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      500))

noncomputable def p8305 :=
@p8298
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p8290
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (p8304
    (@Mathlib.Tactic.Ring.Common.add_pf_add_zero Real Real.instCommSemiring
      (@HAdd.hAdd Real Real Real
        (@instHAdd Real
          (@Distrib.toAdd Real
            (@instDistribOfSemiring Real c0)))
        p8290
        (@OfNat.ofNat Real 0
          (@Zero.toOfNat0 Real
            (@MulZeroClass.toZero Real
              (@instMulZeroClassOfSemiring Real c0)))))))

noncomputable def p8306 :=
p8305
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
      p8290
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))))

noncomputable def p8307 :=
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
    p8290
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p8257
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))

noncomputable def p8308 :=
@Mathlib.Tactic.Ring.Common.mul_add Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    32)
  p8290
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  p8257

noncomputable def p8309 :=
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
    500)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    16000)
  Real.pi

noncomputable def p8310 :=
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
      500))
  16000

noncomputable def p8311 :=
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
    500)
  32 500

noncomputable def p8312 :=
@p8311 16000
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
    500)
  (@Eq.refl Nat 16000)

noncomputable def p8313 :=
@p8308
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p8257
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (p8309
    c9
    (@p8310
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      p8312))
  (@Mathlib.Tactic.Ring.Common.mul_zero Real Real.instCommSemiring
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      32))

noncomputable def p8314 :=
@p8307
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p8257
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (p8313
    (@Mathlib.Tactic.Ring.Common.add_pf_add_zero Real Real.instCommSemiring
      (@HAdd.hAdd Real Real Real
        (@instHAdd Real
          (@Distrib.toAdd Real
            (@instDistribOfSemiring Real c0)))
        p8257
        (@OfNat.ofNat Real 0
          (@Zero.toOfNat0 Real
            (@MulZeroClass.toZero Real
              (@instMulZeroClassOfSemiring Real c0)))))))

noncomputable def p8315 :=
p8314
  (@Mathlib.Tactic.Ring.Common.zero_mul Real Real.instCommSemiring
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))
      p8290
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))))
  (@Mathlib.Tactic.Ring.Common.add_pf_add_zero Real Real.instCommSemiring
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))
      p8257
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))))

noncomputable def p8317 :=
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
    16000)

noncomputable def p8318 :=
@p3730
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    16000)
  (Int.ofNat 16000) (Int.negOfNat 16000) p3731

noncomputable def p8319 :=
p8318
  (@Mathlib.Meta.NormNum.IsNat.to_isInt Real
    (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      16000)
    16000
    (@Mathlib.Meta.NormNum.IsNat.of_raw Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      16000))

noncomputable def p8320 :=
@Mathlib.Tactic.Ring.Common.neg_mul Real Real.commRing Real.pi
  (@Nat.rawCast Nat
    (@AddCommMonoidWithOne.toAddMonoidWithOne Nat
      (@NonAssocSemiring.toAddCommMonoidWithOne Nat
        c34))
    1)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    16000)
  (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (Int.negOfNat 16000))
  (@Mathlib.Meta.NormNum.IsInt.to_raw_eq Real p8317 (Int.negOfNat 16000)
    (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (p8319 (@Eq.refl Int (Int.negOfNat 16000))))

noncomputable def p8321 :=
@Mathlib.Tactic.Ring.Common.neg_add Real Real.commRing p8257
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  p8255
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  p8320 c65

noncomputable def p8331 :=
@Mathlib.Tactic.Ring.Common.mul_congr Real Real.instCommSemiring
  c15

noncomputable def p8332 :=
@p8331
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      800)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  p3713

noncomputable def p8333 :=
@p8332
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
      (Int.negOfNat 50400))
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))
      p8257
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))))

noncomputable def p8334 :=
@Mathlib.Tactic.Ring.cast_pos Real Real.instCommSemiring
  c15

noncomputable def p8335 :=
@Mathlib.Meta.NormNum.isNat_ofNat Real
  c5
  c15

noncomputable def p8336 :=
p8333
  (@p8334 800
    (@p8335 800
      (@Eq.refl Real
        (@OfNat.ofNat Real 800
          (@instOfNatAtLeastTwo Real 800
            (@AddMonoidWithOne.toNatCast Real
              c5)
            (Mathlib.Meta.NormNum.instAtLeastTwo 798))))))

noncomputable def p8337 :=
@Mathlib.Tactic.Ring.Common.add_mul Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    800)
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
      (Int.negOfNat 50400))
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))
      p8257
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))))

noncomputable def p8338 :=
@Mathlib.Tactic.Ring.Common.mul_add Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    800)
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
    (Int.negOfNat 50400))

noncomputable def p8339 :=
@Mathlib.Meta.NormNum.IsInt.to_raw_eq Real
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      800)
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 63)))
  (Int.negOfNat 50400)

noncomputable def p8340 :=
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
    800)
  (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (Int.negOfNat 63))

noncomputable def p8341 :=
@p8340 (Int.ofNat 800) (Int.negOfNat 63) (Int.negOfNat 50400)
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
      800)
    800
    (@Mathlib.Meta.NormNum.IsNat.of_raw Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      800))

noncomputable def p8342 :=
@p8338
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p8257
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 50400))
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))
      p8257
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))))
  (@p8339 (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (p8341
      (@Mathlib.Meta.NormNum.IsInt.of_raw Real
        (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing)) (Int.negOfNat 63))
      (@Eq.refl Int (Int.negOfNat 50400))))

noncomputable def p8343 :=
@Mathlib.Tactic.Ring.Common.mul_add Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    800)
  p3819
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  p8257

noncomputable def p8344 :=
@Mathlib.Tactic.Ring.Common.mul_pf_right Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    800)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    20)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    16000)
  Real.pi

noncomputable def p8345 :=
@Mathlib.Meta.NormNum.IsNat.to_raw_eq Real
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      800)
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      20))
  16000

noncomputable def p8346 :=
@Mathlib.Meta.NormNum.isNat_mul Real c0
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real c0))))
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    800)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    20)
  800 20

noncomputable def p8347 :=
@p8346 16000
  (@Eq.refl (Real → Real → Real)
    (@HMul.hMul Real Real Real
      (@instHMul Real
        (@Distrib.toMul Real
          (@instDistribOfSemiring Real c0)))))
  (@Mathlib.Meta.NormNum.IsNat.of_raw Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    800)
  (@Mathlib.Meta.NormNum.IsNat.of_raw Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    20)
  (@Eq.refl Nat 16000)

noncomputable def p8348 :=
@p8343
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p8257
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (p8344
    c9
    (@p8345
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      p8347))
  (@Mathlib.Tactic.Ring.Common.mul_zero Real Real.instCommSemiring
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      800))

noncomputable def p8349 :=
p8342
  (p8348
    (@Mathlib.Tactic.Ring.Common.add_pf_add_zero Real Real.instCommSemiring
      (@HAdd.hAdd Real Real Real
        (@instHAdd Real
          (@Distrib.toAdd Real
            (@instDistribOfSemiring Real c0)))
        p8257
        (@OfNat.ofNat Real 0
          (@Zero.toOfNat0 Real
            (@MulZeroClass.toZero Real
              (@instMulZeroClassOfSemiring Real c0)))))))

noncomputable def p8350 :=
@Mathlib.Tactic.Ring.Common.add_pf_add_lt Real Real.instCommSemiring
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p8257
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p8257
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (Int.negOfNat 50400))

noncomputable def p8351 :=
p8349
  (p8350
    (@Mathlib.Tactic.Ring.Common.add_pf_zero_add Real Real.instCommSemiring
      (@HAdd.hAdd Real Real Real
        (@instHAdd Real
          (@Distrib.toAdd Real
            (@instDistribOfSemiring Real c0)))
        p8257
        (@OfNat.ofNat Real 0
          (@Zero.toOfNat0 Real
            (@MulZeroClass.toZero Real
              (@instMulZeroClassOfSemiring Real c0)))))))

noncomputable def p8352 :=
@p8337
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 50400))
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))
      p8257
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))))
  p8351

noncomputable def p8353 :=
p8352
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

noncomputable def p8354 :=
p8353
  (@Mathlib.Tactic.Ring.Common.add_pf_add_zero Real Real.instCommSemiring
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))
      (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
        (Int.negOfNat 50400))
      (@HAdd.hAdd Real Real Real
        (@instHAdd Real
          (@Distrib.toAdd Real
            (@instDistribOfSemiring Real c0)))
        p8257
        (@OfNat.ofNat Real 0
          (@Zero.toOfNat0 Real
            (@MulZeroClass.toZero Real
              (@instMulZeroClassOfSemiring Real c0)))))))

noncomputable def p8355 :=
@Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@Mathlib.Meta.NormNum.instAddMonoidWithOne Real
      (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing)))
    50400)
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p8255
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (Int.negOfNat 50400))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p8257
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))

noncomputable def p8356 :=
@Mathlib.Meta.NormNum.isInt_add Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0))))
  (@Nat.rawCast Real
    (@Mathlib.Meta.NormNum.instAddMonoidWithOne Real
      (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing)))
    50400)
  (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (Int.negOfNat 50400))
  (Int.ofNat 50400) (Int.negOfNat 50400)

noncomputable def p8357 :=
@p8356 (Int.ofNat 0)
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
      50400)
    50400
    (@Mathlib.Meta.NormNum.IsNat.of_raw Real
      (@Mathlib.Meta.NormNum.instAddMonoidWithOne Real
        (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing)))
      50400))
  (@Mathlib.Meta.NormNum.IsInt.of_raw Real
    (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing)) (Int.negOfNat 50400))

noncomputable def p8358 :=
@Mathlib.Meta.NormNum.IsInt.to_isNat Real
  (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@Mathlib.Meta.NormNum.instAddMonoidWithOne Real
        (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing)))
      50400)
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 50400)))
  0 (p8357 (@Eq.refl Int (Int.ofNat 0)))

noncomputable def p8359 :=
@Mathlib.Meta.NormNum.isInt_add Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0))))
  (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (Int.negOfNat 16000))
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    16000)
  (Int.negOfNat 16000) (Int.ofNat 16000)

noncomputable def p8360 :=
@p8359 (Int.ofNat 0)
  (@Eq.refl (Real → Real → Real)
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))))
  (@Mathlib.Meta.NormNum.IsInt.of_raw Real
    (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing)) (Int.negOfNat 16000))
  (@Mathlib.Meta.NormNum.IsNat.to_isInt Real
    (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      16000)
    16000
    (@Mathlib.Meta.NormNum.IsNat.of_raw Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      16000))

noncomputable def p8361 :=
@Mathlib.Meta.NormNum.IsInt.to_isNat Real
  (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 16000))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      16000))
  0 (p8360 (@Eq.refl Int (Int.ofNat 0)))

noncomputable def p8362 :=
@Mathlib.Tactic.Ring.Common.add_overlap_pf_zero Real Real.instCommSemiring
  (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (Int.negOfNat 16000))
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    16000)
  Real.pi
  (@Nat.rawCast Nat
    (@AddCommMonoidWithOne.toAddMonoidWithOne Nat
      (@NonAssocSemiring.toAddCommMonoidWithOne Nat
        c34))
    1)
  p8361

noncomputable def p8363 :=
@Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero Real Real.instCommSemiring p8255
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  p8257
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  p8362

noncomputable def p8371 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  (@OfNat.ofNat Real 500
    (@instOfNatAtLeastTwo Real 500
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8380 :=
@Mathlib.Tactic.CancelDenoms.sub_subst Real
  c32
  (@OfNat.ofNat Real 500
    (@instOfNatAtLeastTwo Real 500
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8384 :=
@Mathlib.Tactic.CancelDenoms.div_subst Real Real.instField
  (@OfNat.ofNat Real 1
    (@One.toOfNat1 Real
      (@AddMonoidWithOne.toOne Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))))
  (@OfNat.ofNat Real 500
    (@instOfNatAtLeastTwo Real 500
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8385 :=
@p8384
  (@OfNat.ofNat Real 500
    (@instOfNatAtLeastTwo Real 500
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8387 :=
@HDiv.hDiv Real Real Real
  c62
  (@OfNat.ofNat Real 500
    (@instOfNatAtLeastTwo Real 500
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8388 :=
@Mathlib.Meta.NormNum.isNat_eq_true Real
  (@Mathlib.Meta.NormNum.instAddMonoidWithOne' Real
    (@DivisionSemiring.toSemiring Real
      c3))
  (p8387 p4068)
  (@OfNat.ofNat Real 1
    (@One.toOfNat1 Real
      (@AddMonoidWithOne.toOne Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))))
  1

noncomputable def p8389 :=
@Mathlib.Meta.NormNum.isNNRat_div Real
  c3
  (@OfNat.ofNat Real 500
    (@instOfNatAtLeastTwo Real 500
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8390 :=
p8250
  (@Inv.inv Real
    (@InvOneClass.toInv Real
      (@DivInvOneMonoid.toInvOneClass Real
        (@DivisionMonoid.toDivInvOneMonoid Real
          (@GroupWithZero.toDivisionMonoid Real
            (@DivisionSemiring.toGroupWithZero Real
              c3)))))
    p4068)

noncomputable def p8391 :=
@HMul.hMul Real Real Real
  c19
  (@OfNat.ofNat Real 500
    (@instOfNatAtLeastTwo Real 500
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8392 :=
p8391
  (@Inv.inv Real
    (@InvOneClass.toInv Real
      (@DivInvOneMonoid.toInvOneClass Real
        (@DivisionMonoid.toDivInvOneMonoid Real
          (@GroupWithZero.toDivisionMonoid Real
            (@DivisionSemiring.toGroupWithZero Real
              c3)))))
    p4068)

noncomputable def p8393 :=
@Mathlib.Meta.NormNum.isNNRat_mul Real
  (@DivisionSemiring.toSemiring Real
    c3)
  (@HMul.hMul Real Real Real
    c19)
  (@OfNat.ofNat Real 500
    (@instOfNatAtLeastTwo Real 500
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8394 :=
@p8393
  (@Inv.inv Real
    (@InvOneClass.toInv Real
      (@DivInvOneMonoid.toInvOneClass Real
        (@DivisionMonoid.toDivInvOneMonoid Real
          (@GroupWithZero.toDivisionMonoid Real
            (@DivisionSemiring.toGroupWithZero Real
              c3)))))
    p4068)

noncomputable def p8395 :=
@Mathlib.Meta.NormNum.IsNat.to_isNNRat Real
  (@DivisionSemiring.toSemiring Real
    c3)
  (@OfNat.ofNat Real 500
    (@instOfNatAtLeastTwo Real 500
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8396 :=
@p8394 500 1 1 1 500 1 500
  (@Eq.refl (Real → Real → Real)
    (@HMul.hMul Real Real Real
      c19))
  (@p8395 500
    (@p8295 500
      (@Eq.refl Real
        (@OfNat.ofNat Real 500
          (@instOfNatAtLeastTwo Real 500
            (@AddMonoidWithOne.toNatCast Real
              c5)
            (Mathlib.Meta.NormNum.instAtLeastTwo 498))))))

noncomputable def p8397 :=
@Mathlib.Meta.NormNum.IsNNRat.to_isNat Real
  (@DivisionSemiring.toSemiring Real
    c3)
  (p8387 p4068) 1
  (@p8389 p4068 1 1
    (@Mathlib.Meta.NormNum.IsNat.to_isNNRat Real
      (@DivisionSemiring.toSemiring Real
        c3)
      p8390 1
      (@Mathlib.Meta.NormNum.IsNNRat.to_isNat Real
        (@DivisionSemiring.toSemiring Real
          c3)
        p8392 1
        (p8396 p4091 (@Eq.refl Nat (Nat.mul 500 1))
          (@Eq.refl Nat 500)))))

noncomputable def p8398 :=
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
  (@OfNat.ofNat Real 500
    (@instOfNatAtLeastTwo Real 500
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8399 :=
@Mathlib.Meta.NormNum.isNat_eq_true Real
  c5
  p8398
  (@OfNat.ofNat Real 500
    (@instOfNatAtLeastTwo Real 500
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8400 :=
@Mathlib.Meta.NormNum.isNat_mul Real Real.semiring
  (@HMul.hMul Real Real Real
    c19)
  (@OfNat.ofNat Real 1
    (@One.toOfNat1 Real
      (@AddMonoidWithOne.toOne Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))))
  (@OfNat.ofNat Real 500
    (@instOfNatAtLeastTwo Real 500
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8401 :=
@p8400 1 500 500
  (@Eq.refl (Real → Real → Real)
    (@HMul.hMul Real Real Real
      c19))
  (p3747
    (@Nat.cast_one Real
      c5))
  (@p8295 500
    (@Eq.refl Real
      (@OfNat.ofNat Real 500
        (@instOfNatAtLeastTwo Real 500
          (@AddMonoidWithOne.toNatCast Real
            c5)
          (Mathlib.Meta.NormNum.instAtLeastTwo 498)))))
  (@Eq.refl Nat 500)

noncomputable def p8403 :=
@Mathlib.Tactic.CancelDenoms.mul_subst Real (@Field.toCommRing Real Real.instField)
  (@OfNat.ofNat Real 1
    (@One.toOfNat1 Real
      (@AddMonoidWithOne.toOne Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))))
  (@OfNat.ofNat Real 500
    (@instOfNatAtLeastTwo Real 500
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8404 :=
@p8403
  (@OfNat.ofNat Real 500
    (@instOfNatAtLeastTwo Real 500
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8405 :=
@p8404
  c21
  Real.pi p3705 (p8250 Real.pi)

noncomputable def p8406 :=
@HMul.hMul Real Real Real
  (@instHMul Real
    (@inferInstance (Mul Real)
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real
          (@DivisionSemiring.toSemiring Real
            c3)))))
  (@OfNat.ofNat Real 500
    (@instOfNatAtLeastTwo Real 500
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8407 :=
p8405 (@rfl Real p3930) (@rfl Real (p8406 Real.pi))
  (@p8399 500 p8401
    (@p8295 500
      (@Eq.refl Real
        (@OfNat.ofNat Real 500
          (@instOfNatAtLeastTwo Real 500
            (@AddMonoidWithOne.toNatCast Real
              c5)
            (Mathlib.Meta.NormNum.instAtLeastTwo 498))))))

noncomputable def p8411 :=
@Mathlib.Meta.NormNum.isNat_lt_true Real Real.semiring Real.partialOrder Real.instIsOrderedRing
  (@FloorSemiring.instCharZero Real (@Ring.toSemiring Real Real.instRing) Real.partialOrder
    c26)
  c25
  (@OfNat.ofNat Real 500
    (@instOfNatAtLeastTwo Real 500 Real.instNatCast
      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 499 (instOfNatNat 499))
        c63)))
  0 500
  (@Mathlib.Meta.NormNum.isNat_ofNat Real
    c5
    c25 0
    (@Nat.cast_zero Real
      c5))

noncomputable def p8412 :=
p8411
  (@Mathlib.Meta.NormNum.isNat_ofNat Real
    c5
    (@OfNat.ofNat Real 500
      (@instOfNatAtLeastTwo Real 500 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 499 (instOfNatNat 499))
          c63)))
    500
    (@Eq.refl Real
      (@OfNat.ofNat Real 500
        (@instOfNatAtLeastTwo Real 500
          (@AddMonoidWithOne.toNatCast Real
            c5)
          (Mathlib.Meta.NormNum.instAtLeastTwo 498)))))

noncomputable def p8413 :=
@Mathlib.Meta.NormNum.isNat_lt_true Real Real.semiring Real.partialOrder Real.instIsOrderedRing
  (@FloorSemiring.instCharZero Real (@Ring.toSemiring Real Real.instRing) Real.partialOrder
    c26)
  c25
  (@OfNat.ofNat Real 800
    (@instOfNatAtLeastTwo Real 800 Real.instNatCast
      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 799 (instOfNatNat 799))
        (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 798 (instOfNatNat 798))))))
  0 800
  (@Mathlib.Meta.NormNum.isNat_ofNat Real
    c5
    c25 0
    (@Nat.cast_zero Real
      c5))

noncomputable def p8414 :=
p8413
  (@Mathlib.Meta.NormNum.isNat_ofNat Real
    c5
    (@OfNat.ofNat Real 800
      (@instOfNatAtLeastTwo Real 800 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 799 (instOfNatNat 799))
          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 798 (instOfNatNat 798))))))
    800
    (@Eq.refl Real
      (@OfNat.ofNat Real 800
        (@instOfNatAtLeastTwo Real 800
          (@AddMonoidWithOne.toNatCast Real
            c5)
          (Mathlib.Meta.NormNum.instAtLeastTwo 798)))))

noncomputable def p9404 :=
nat_lit 1902320482601297510400000000

theorem d196 : Enclosure.Real.IsNear Real.pi false 226375608064910080 72057594037927936 1
  1000000000000000 :=
BSN.pi_near_15

theorem d197 : p2306 500000000000000 :=
@p501 1 1000000000000000 884279719003555 140737488355328
  1 500000000000000 (Enclosure.Real.IsNear.const false 2 1)
  d196 (Eq.refl true)

noncomputable def p11843 :=
Enclosure.Real.IsNear
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi))
  false 11199533475045 70368744177664

noncomputable def p11844 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
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
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 96 1)
      c16))
  false 74269213037

noncomputable def p11849 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 96 1)
      c16))
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

noncomputable def p12231 :=
nat_lit 601226901190101306339707032778070279008174732520529886901066488712245510429339761526706943586500787976175353856

noncomputable def p12257 :=
nat_lit
  27606985387162255149739023449108101809804435888681546220650096895197184000000000000000000000000000000000000000000

noncomputable def p12261 :=
nat_lit 24519928653854221733733552434404946937899825954937634816

noncomputable def p12263 :=
nat_lit 913438523331814323877303020447676887284957839360000000000000000000000000000

noncomputable def p12265 :=
nat_lit 4951760157141521099596496896

noncomputable def p12267 :=
nat_lit 30223145490365729367654400000000000000

noncomputable def p12284 :=
nat_lit 696898287454081973172991196020261297061888

noncomputable def p12286 :=
nat_lit 21267647932558653966460912964485513216000000000000000

noncomputable def p12314 :=
nat_lit 348449143727040986586495598010130648530944

noncomputable def p12316 :=
nat_lit 64903710731685345356631204115251200000000000000000000000000000

noncomputable def p12348 :=
nat_lit 1947976174183728650649600000000000000000000000

noncomputable def p12357 :=
nat_lit
  12314720538252212013175536584546949912589922018805340084673386748512714874007374005243903479319278300245823356305175174303539820705499876134073153122420792581317882717422223006813658783748121083660254535082634382113709149488299688196491642633853971843408327376193589307780822967796105216000

noncomputable def p12359 :=
nat_lit
  701939070680376084751005585319176145017625555071904384826383044665224747818420318298902498321198863114011931309394984935301769780213492939642169727977985177135119314893066711388378550673642901768634508499710159780481421520833082227200023630129676395074274660443034590543506909164377997312000

noncomputable def p12373 :=
nat_lit 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288

noncomputable def p12381 :=
nat_lit 1725436586697640946858688965569256363112777243042596638790631055949824

noncomputable def p12388 :=
nat_lit 431359146674410236714672241392314090778194310760649159697657763987456

noncomputable def p12402 :=
nat_lit 973988087091864325324800000000000000000000000

noncomputable def p12450 :=
nat_lit 1393796574908163946345982392040522594123776

noncomputable def p13484 :=
nat_lit
  6838086273244272776046602705939160397930937163857986759345297528214257717227530526065271529703858682961073775246997836382095498910209370425301137744140125182879779952975499837341102371407

noncomputable def p13485 :=
nat_lit
  2175541218577478036232553294038911497542013410209922757424923190068852981190050786259609609278379154099770693575665668158859588967025488852621393833027941793561932885341770625153958412288

noncomputable def p13486 :=
Enclosure.Real.IsNear
  (hardyZApproximantRS
    (@OfScientific.ofScientific Real c2 101532600
      true 5))
  false p13484 p13485

noncomputable def p13487 :=
nat_lit
  6800200211533130392580661143727020570957607639447307571216755405847041294432414489338296191062362952338071275018221976992355020317552177396959625741885758166612428518349565425209544218802693816719689078136122604957958854442145902703642871

noncomputable def p13488 :=
nat_lit
  2107795099709022023703331017312974732662759536289867565607301194835517248595560125098914389927906113265023745682732141615964551146191745335896757464417499648096877936640000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p13489 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZApproximantRS
    (@OfScientific.ofScientific Real c2 101532600
      true 5))
  (hardyZApproximantRS
    (@OfScientific.ofScientific Real c2 101532600
      true 5))
  false p13484

noncomputable def p13490 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
  (Zeta.RiemannSiegel.mainSumOfPhase
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101532600
        true 5))
    (@OfScientific.ofScientific Real c2 101532600
      true 5)
    12)

noncomputable def p13491 :=
@HPow.hPow Real Real Real (@instHPow Real Real Real.instPow)
  (@HDiv.hDiv Real Real Real c4
    (@OfScientific.ofScientific Real c2 101532600
      true 5)
    c7)

noncomputable def p13492 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  c22
  (p13491
    (@Neg.neg Real Real.instNeg
      (@HDiv.hDiv Real Real Real c4
        c38
        c20)))

noncomputable def p13493 :=
Real.sqrt
  (@HDiv.hDiv Real Real Real c4
    (@OfScientific.ofScientific Real c2 101532600
      true 5)
    c7)

noncomputable def p13494 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p13492
  (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
        (Enclosure.sfrac false 12 1)))
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Zeta.RiemannSiegel.correctionLinear
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
          (Enclosure.sfrac false 12 1)))
      (@Inv.inv Real Real.instInv p13493)))

noncomputable def p13495 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZApproximantRS
    (@OfScientific.ofScientific Real c2 101532600
      true 5))
  (p13490 p13494) false p13484

noncomputable def p13496 :=
@BSN.floor_sqrt_eq_dec
  (@OfScientific.ofScientific Real c2 101532600
    true 5)
  101532600 100000 12
  (Enclosure.sfrac_ofScientific_eq 101532600 5 100000 (Eq.refl true))

noncomputable def p13497 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (Zeta.RiemannSiegel.mainSumOfPhase
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101532600
        true 5))
    (@OfScientific.ofScientific Real c2 101532600
      true 5)
    12)

noncomputable def p13498 :=
nat_lit
  283539949682863571565831929805252393781414552109651661775408137968580206080752072994075230644277941118604652944486172587567296584504261322349154774722643433700844765678103927615953964465

noncomputable def p13499 :=
nat_lit
  109985538849443650398143445426492249266869779745201156226294759986553128372372163838988580876211001526737766542623195841138834681766210675725350937529131055004108518349565425209544218802693816719689078136122604957958854442145902703642871

noncomputable def p13500 :=
nat_lit
  58738713821621342784846581587827597749623442370802092639578150510139748352815718800584033562875931216646888611458220058887718255536305772978835995125346106603629347995412379381266708563562221010944

noncomputable def p13501 :=
@p13497 p13494 28119119473 8589934592 109059
  34359738368 p13498 p13485 p13499
  p13488 p13500 p13484

noncomputable def p13502 :=
@Enclosure.Real.IsNear.of_eq
  (Zeta.RiemannSiegel.mainSumOfPhase
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101532600
        true 5))
    (@OfScientific.ofScientific Real c2 101532600
      true 5)
    12)

noncomputable def p13503 :=
@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101532600
        true 5))
    (@OfScientific.ofScientific Real c2 101532600
      true 5)
    12)

noncomputable def p13504 :=
p13503
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101532600
        true 5))
    (@OfScientific.ofScientific Real c2 101532600
      true 5)
    12)

noncomputable def p13505 :=
@p13502 p13504 false 28119119473 8589934592
  109059 34359738368
  (BSN.main_sum_of_phase_eq
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101532600
        true 5))
    (@OfScientific.ofScientific Real c2 101532600
      true 5)
    12)

noncomputable def p13506 :=
@Enclosure.Real.IsNear.addLit_ff
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101532600
        true 5))
    (@OfScientific.ofScientific Real c2 101532600
      true 5)
    12)

noncomputable def p13507 :=
@p13506
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101532600
        true 5))
    (@OfScientific.ofScientific Real c2 101532600
      true 5)
    12)

noncomputable def p13508 :=
@p13507 224952955784 137438953472 218118 137438953472
  224952955784 137438953472 218118 137438953472
  61834597646772098564096 28119119473 8589934592

noncomputable def p13509 :=
BSN.mainSumRS_step
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real c2 101532600
      true 5))
  (@OfScientific.ofScientific Real c2 101532600
    true 5)
  Real.cos BSN.quadSignNeg

noncomputable def p13510 :=
p13509 11 12 101532600 100000 286
  137438953472 68719476736 2305843009213693952 false 284973530396075
  3364

noncomputable def p13511 :=
p13510 341522969406 43 39675208392 8 false
  263002523384 204533 true 39479503148 7244019458077122842 1

noncomputable def p13512 :=
p13511 false 131807568577 true false 224952955784 218118
  BSN.abs_quadSignNeg (BSN.cos_quad_nat2 286 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 131807568577 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101532600 5 100000 (Eq.refl true))
  (Eq.refl true)

noncomputable def p13513 :=
BSN.mainSumRS_step2
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real c2 101532600
      true 5))
  (@OfScientific.ofScientific Real c2 101532600
    true 5)
  Real.cos Real.sin

noncomputable def p13514 :=
p13513 BSN.quadSignPos BSN.quadSignNeg 9 10 11 101532600
  100000 168 229 137438953472 68719476736

noncomputable def p13515 :=
p13514 2305843009213693952 false 284973530396075 3364
  316464885454 43 43462013224 8 329564216814 43
  41439403656

noncomputable def p13516 :=
p13515 8 false 266662604643 175466 true 72210542637
  true 203097455447 7244019458077122842 1 false

noncomputable def p13517 :=
p13516 118901594537 false false 136844160670 true false
  263002523384 204533 BSN.abs_quadSignPos
  (BSN.cos_quad_nat0 168 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 118901594537 137438953472)

noncomputable def p13518 :=
BSN.mainSumRS_step2
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real c2 101532600
      true 5))
  (@OfScientific.ofScientific Real c2 101532600
    true 5)
  Real.cos Real.cos

noncomputable def p13519 :=
p13518 BSN.quadSignPos BSN.quadSignPos 7 8 9 101532600
  100000 24 100 137438953472 68719476736

noncomputable def p13520 :=
p13519 2305843009213693952 false 284973530396075 3364
  285796269294 43 48592008000 16 301984246446 43
  45812984488

noncomputable def p13521 :=
p13520 8 false 175858617789 143139 true 21526042588
  true 50066283721 7244019458077122842 1 false

noncomputable def p13522 :=
p13521 135756664568 false false 128420273409 false false
  266662604643 175466 BSN.abs_quadSignPos
  (BSN.cos_quad_nat0 24 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 135756664568 137438953472)

noncomputable def p13523 :=
BSN.mainSumRS_step2
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real c2 101532600
      true 5))
  (@OfScientific.ofScientific Real c2 101532600
    true 5)
  Real.sin Real.cos

noncomputable def p13524 :=
p13523 BSN.quadSignNeg BSN.quadSignNeg 5 6 7 101532600
  100000 161 62 137438953472 68719476736

noncomputable def p13525 :=
p13524 2305843009213693952 false 284973530396075 3364
  246257546308 43 56109217800 8 267443854420 43
  51947041624

noncomputable def p13526 :=
p13525 8 false 279540183044 106149 false
  183775806509 false 45738060348 7244019458077122842 1 false

noncomputable def p13527 :=
p13526 133704390888 true false 129898389260 true false
  175858617789 143139 BSN.abs_quadSignNeg
  (BSN.cos_quad_nat1 161 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 133704390888 137438953472)

noncomputable def p13528 :=
BSN.mainSumRS_step2
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real c2 101532600
      true 5))
  (@OfScientific.ofScientific Real c2 101532600
    true 5)
  Real.sin Real.sin

noncomputable def p13529 :=
p13528 BSN.quadSignPos BSN.quadSignPos 3 4 5 101532600
  100000 423 279 137438953472 68719476736

noncomputable def p13530 :=
p13529 2305843009213693952 false 284973530396075 3364
  190530846192 42 68719476728 8 221199462352 42
  61464568544

noncomputable def p13531 :=
p13530 16 false 156435428477 62542 false
  201729271131 false 151044771081 7244019458077122842 1 false

noncomputable def p13532 :=
p13531 136710232031 false false 122423913563 false false
  279540183044 106149 BSN.abs_quadSignPos
  (BSN.cos_quad_nat3 423 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 136710232031 137438953472)

noncomputable def p13533 :=
p13528 BSN.quadSignPos BSN.quadSignNeg 1 2 3 101532600
  100000 871 609 137438953472 68719476736

noncomputable def p13534 :=
p13533 2305843009213693952 false 284973530396075 3364
  95265423088 42 97184016000 16 150992123216 42
  79350416784

noncomputable def p13535 :=
p13534 16 false 137437754520 3410 false 209095983609
  false 191142506804 7244019458077122842 1 false

noncomputable def p13536 :=
p13535 137271132450 false false 135217178940 true false
  156435428477 62542 BSN.abs_quadSignPos
  (BSN.cos_quad_nat3 871 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 137271132450 137438953472)

noncomputable def p13537 :=
@Enclosure.Real.IsNear.recentre'
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101532600
        true 5))
    (@OfScientific.ofScientific Real c2 101532600
      true 5)
    1)

noncomputable def p13538 :=
@Enclosure.Real.IsNear.of_eq
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101532600
        true 5))
    (@OfScientific.ofScientific Real c2 101532600
      true 5)
    1)

noncomputable def p13539 :=
@p13538
  (Real.cos
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101532600
        true 5)))
  false 17179719315

noncomputable def p13540 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101532600
        true 5)))
  false 17179719315

noncomputable def p13541 :=
@Enclosure.Real.IsNear.cos_image
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real c2 101532600
      true 5))
  (@HDiv.hDiv Real Real Real c4
    (@Nat.cast Real Real.instNatCast 35621691299509)
    (@Nat.cast Real Real.instNatCast 17179869184))
  false 35621691299509

noncomputable def p13542 :=
nat_lit 12787858787795785018081607634875036805659172382381895117

noncomputable def p13543 :=
nat_lit 6167414659528586025790317767973891577473183902597120

noncomputable def p13544 :=
@Enclosure.Real.IsNear.recentre'
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real c2 101532600
      true 5))
  false p13542 p13543

noncomputable def p13545 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 101532600 400000)
      (Real.log (Enclosure.sfrac false 41235485451040000 160000000000)))
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 1 4)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 1 2) Real.pi)
        (Real.arctan
          (@HDiv.hDiv Real Real Real c4
            (@Nat.cast Real Real.instNatCast 100000)
            (@Nat.cast Real Real.instNatCast 203065200))))))

noncomputable def p13546 :=
nat_lit 517927584496939917014310597780480000000000000000

noncomputable def p13547 :=
nat_lit 3155192413018839615239861581799517818880000000000000

noncomputable def p13548 :=
@Enclosure.Real.IsNear.of_eq
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real c2 101532600
      true 5))
  (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (p13545 (Enclosure.sfrac false 101532600 200000))
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 101532600 200000) (Real.log Real.pi)))
    (Enclosure.sfrac true p13546 p13547))
  false

noncomputable def p13549 :=
BSN.riemannSiegelThetaApproximant_two_zero_mk
  (@OfScientific.ofScientific Real c2 101532600
    true 5)
  101532600 100000 41235485451040000 160000000000

noncomputable def p13550 :=
p13549 203065200 400000 200000 p13546
  p13547
  (Enclosure.sfrac_ofScientific_eq 101532600 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p13551 :=
@Enclosure.Real.IsNear.addLit_ft_p
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (p13545 (Enclosure.sfrac false 101532600 200000))
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 101532600 200000) (Real.log Real.pi)))
  (Enclosure.sfrac true p13546 p13547) 747041070663072506513
  360287970189639680

noncomputable def p13552 :=
nat_lit 2357058131766519094532801919260166784019098653520630907965440000000000000

noncomputable def p13553 :=
@p13551 846730078374775459 p3054 p13546
  p13547 0 1 p13552 p13542
  p13543 846730078374775459 p3054

noncomputable def p13554 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (p13545 (Enclosure.sfrac false 101532600 200000))
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 101532600 200000) (Real.log Real.pi))
  23910443592254747025449 9007199254740992000 639863557193 66000000000000000000

noncomputable def p13555 :=
nat_lit 1283406786906688580140032799539200000

noncomputable def p13556 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 101532600 400000)
      (Real.log (Enclosure.sfrac false 41235485451040000 160000000000)))
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 1 4)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 1 2) Real.pi)
        (Real.arctan
          (@HDiv.hDiv Real Real Real c4
            (@Nat.cast Real Real.instNatCast 100000)
            (@Nat.cast Real Real.instNatCast 203065200))))))

noncomputable def p13557 :=
@p13556 (Enclosure.sfrac false 101532600 200000)
  5696613077502864649429 1801439850948198400 639863557193 66000000000000000000
  101532600 200000 0

noncomputable def p13558 :=
nat_lit 956417743690189881017960000

noncomputable def p13559 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 101532600 400000)
    (Real.log (Enclosure.sfrac false 41235485451040000 160000000000)))
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 1 4)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 1 2) Real.pi)
      (Real.arctan
        (@HDiv.hDiv Real Real Real c4
          (@Nat.cast Real Real.instNatCast 100000)
          (@Nat.cast Real Real.instNatCast 203065200)))))
  5697320279497165605429

noncomputable def p13560 :=
nat_lit 12827632266557897842681215752068923392

noncomputable def p13561 :=
@p13559 1801439850948198400 211621182981 22000000000000000000
  884002492876195 2251799813685248 20000033 264000000000000000
  p13560 5696613077502864649429 1801439850948198400 639863557193

noncomputable def p13562 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 101532600 400000)
  (Real.log (Enclosure.sfrac false 41235485451040000 160000000000)) 101532600
  400000 0 1 56113211712269415 4503599627370496

noncomputable def p13563 :=
nat_lit 30848564374748326318854635520

noncomputable def p13564 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv Real Real Real c4
      (@Nat.cast Real Real.instNatCast 41235485451040000)
      (@Nat.cast Real Real.instNatCast 160000000000)))
  false p13563 p2333

noncomputable def p13565 :=
BSN.log_rat_reduce_isNear 41235485451040000 160000000000 17 82470970902080000
  41943040000000000 46463564802 68719476736 24973259072661432
  36028797018963968 26400000000 1000000000000000

noncomputable def p13566 :=
nat_lit
  921453154010720706122778922173896980873657862648455676281772382698502240472326873134021724686962797476959567218802667873979229172620428115071258195363963624974978755274335035074718577128451469041627842931208361929378912019841490788913168456995417849984690652404228841683033912850583562223616000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p13567 :=
nat_lit
  34839473259413528692013038553947687028407014235153879231220923050437948672460109462674608288656865663367535729921087444821325019149250859293357299679676981895452788046454364034302406827585421891667416402077452379029718647549963535792389117336705698479082374879740606723066144381635867023769600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p13568 :=
nat_lit
  769517536605411750913787895361102133528720476367754811149066690346118209834796075300825296421389917890019197878202274998814833292413962119568122747876870948332710434888589243776055639791782803486527866889241356407387869865441920206485022601272658647726773065030528587157148270592000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p13569 :=
BSN.log_dyadic_bound 20263965451040000 62207005451040000 12 11
  p13566 68719476736 26400000000 p13567 p13568
  46463564802 82470970902080000

noncomputable def p13570 :=
p13569 41943040000000000 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p13571 :=
@BSN.binarySplit_of_base11 (BSN.artanhP 20263965451040000) (BSN.artanhQ 62207005451040000)
  0 11 p13567 p13566 p13568
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p13572 :=
p13565 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p13570 (p13571 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

noncomputable def p13573 :=
@p13562 1250561 33000000000000000 5697320279497165605429
  1801439850948198400 211621182981 22000000000000000000
  (Enclosure.Real.IsNear.const false 101532600 400000)
  (BSN.isNear_log_sfrac 41235485451040000 160000000000 56113211712269415
    4503599627370496 1250561 33000000000000000 false
    (@p13564 1000448800000000 p2422 56113211712269415
      4503599627370496 1250561 33000000000000000
      (p13572 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p13574 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 1 4)
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 1 2) Real.pi)
    (Real.arctan
      (@HDiv.hDiv Real Real Real c4
        (@Nat.cast Real Real.instNatCast 100000)
        (@Nat.cast Real Real.instNatCast 203065200))))
  1 4

noncomputable def p13575 :=
@p13574 0 1 884002492876195 562949953421312 20000033
  66000000000000000 884002492876195 2251799813685248 20000033
  264000000000000000 (Enclosure.Real.IsNear.const false 1 4)

noncomputable def p13576 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 1 2) Real.pi)
  (Real.arctan
    (@HDiv.hDiv Real Real Real c4
      (@Nat.cast Real Real.instNatCast 100000) (@Nat.cast Real Real.instNatCast 203065200)))
  884279719003555 562949953421312 1

noncomputable def p13577 :=
nat_lit 7593523592971461003837440

noncomputable def p13578 :=
@p13576 2000000000000000 4230135 8589934592 1
  3300000000 p13577 884002492876195 562949953421312 20000033
  66000000000000000
  (@p803 1 1000000000000000 884279719003555 562949953421312
    1 2000000000000000 (Enclosure.Real.IsNear.const false 1 2)
    BSN.pi_near_15 (Eq.refl true))

noncomputable def p13579 :=
BSN.arctan_dyadic_bound_f 100000 203065200 1 0 8589934592
  3300000000 0 1 1 0 1

noncomputable def p13580 :=
p13579 1 4230135 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)
  (@BSN.binarySplit_of_le (BSN.arctanEvenP 100000) (BSN.arctanEvenQ 203065200) 0
    0 (Eq.refl true))
  (@BSN.binarySplit_of_le (BSN.arctanOddP 100000) (BSN.arctanOddQ 203065200) 0 0
    (Eq.refl true))

noncomputable def p13581 :=
p13575
  (p13578
    (p13580 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p13582 :=
@p13554 39935431104110217 68719476736000 507663 34359738368000
  p13555 747041070663072506513 360287970189639680 846730078374775459
  p3054
  (@p13557 1 p13558 23910443592254747025449
    9007199254740992000 639863557193 66000000000000000000
    (@p13561 66000000000000000000 p13573 p13581
      (Eq.refl true) (Eq.refl true))
    (Enclosure.Real.IsNear.const false 101532600 200000) (Eq.refl true)
    (Eq.refl true))

noncomputable def p13583 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 101532600 200000) (Real.log Real.pi)
  101532600 200000 0 1 78665238759 68719476736

noncomputable def p13584 :=
p13582
  (@p13583 1 34359738368 39935431104110217 68719476736000
    507663 34359738368000
    (Enclosure.Real.IsNear.const false 101532600 200000) d91
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p13585 :=
@p13541 17179869184 421 17179869184 false 17179719315
  17179869184 1 3300000000
  (@p13544 846730078374775459 p3054 35621691299509
    17179869184 421 17179869184
    (@p13548 p13542 p13543 846730078374775459
      p3054
      (p13550 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p13553 (p13584 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p13546 p13547)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p13586 :=
nat_lit 10341644052365568741736448

noncomputable def p13587 :=
BSN.cos_reduce0
  (@HDiv.hDiv Real Real Real c4
    (@Nat.cast Real Real.instNatCast 35621691299509)
    (@Nat.cast Real Real.instNatCast 17179869184))
  (@HDiv.hDiv Real Real Real c4
    (@Nat.cast Real Real.instNatCast p13586)
    (@Nat.cast Real Real.instNatCast p2333))
  226375608064910080 72057594037927936 false

noncomputable def p13588 :=
BSN.sin_reduce_arg_pos_rat_q0 35621691299509 17179869184 226375608064910080
  72057594037927936 330 p13586 p2333
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p13589 :=
BSN.cos_dyadic_bound_f 146963601144 35184372088832 1 0 17179869184
  6606445313 0 1 1 0 1

noncomputable def p13590 :=
p13589 1 17179719315 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (@BSN.binarySplit_of_le (BSN.cosEvenP 146963601144) (BSN.cosEvenQ 35184372088832) 0
    0 (Eq.refl true))

noncomputable def p13591 :=
p13590
  (@BSN.binarySplit_of_le (BSN.cosOddP 146963601144) (BSN.cosOddQ 35184372088832) 0
    0 (Eq.refl true))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p13592 :=
@BSN.cos_arg_round false 17179719315 17179869184 p13586
  p2333 146963601144 35184372088832 6606445313 6600000000
  p13591 (Eq.refl true)

noncomputable def p13593 :=
p13587 17179719315 17179869184 330 1000000000000000
  6600000000 3300000000 p13588 BSN.pi_near_15 p13592
  (Eq.refl true) (Eq.refl true)

noncomputable def p13594 :=
@p13539 17179869184 5494061989 221459251200000000
  (BSN.main_sum_rs_one
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101532600
        true 5))
    (@OfScientific.ofScientific Real c2 101532600
      true 5))
  (@p13540 17179869184 1406479869184 56693568307200000000
    17179719315 17179869184 5494061989 221459251200000000
    (p13585 (Enclosure.sfrac_false_div 35621691299509 17179869184)
      (p13593 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p13595 :=
@p13537 false 17179719315 17179869184 5494061989
  221459251200000000 137437754520 137438953472 3410 137438953472
  p13594 (Eq.refl true)

noncomputable def p13596 :=
p13536 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 609 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 135217178940 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101532600 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true) p13595
  (@p13544 846730078374775459 p3054 284973530396075
    137438953472 3364 137438953472
    (@p13548 p13542 p13543 846730078374775459
      p3054
      (p13550 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p13553 (p13584 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p13546 p13547)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p13597 :=
nat_lit
  12651135233285105609149196585531872231458705697583091606552677408782392331488585432669111571631317244068825881820066595345693801088907452162081

noncomputable def p13598 :=
nat_lit
  6984708560842165324835505347390308205368889464422370172233101077046117557660308096260491610151199430342708233706520799452252691681845281

noncomputable def p13599 :=
nat_lit
  63186495645614598888708302737376011243078820275456782607000282294532257522908966023880755139389932759877237304859237305324043582812750753374241

noncomputable def p13600 :=
BSN.sin_dyadic_bound_f 209095983609 137438953472 4 3 137438953472
  68719476736 p13597 p2504 p13598
  p13599 p2507

noncomputable def p13601 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 209095983609) (BSN.sinEvenQ 137438953472) 0
  3 p13597 p2504 p13598 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p13602 :=
p13600 p13598 137271132450 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p13601 (Eq.refl true))

noncomputable def p13603 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 209095983609) (BSN.sinOddQ 137438953472) 0
  3 p13599 p2507 p13598 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p13604 :=
nat_lit
  8829659397581064452151124471772521221454347772485312618897835744342194452608152760891788775022564150404311513609083194735381308197468284911616

noncomputable def p13605 :=
nat_lit
  2378413323038473551418947953843698147277668079109086701644903428946550095500110132689452543137812582962994194116512894315818822051823616

noncomputable def p13606 :=
nat_lit
  44114566423954496335224759968415145418633576975566544703825560362061939459898879768342138078614009248170054860740568028157450091527340321406976

noncomputable def p13607 :=
BSN.sin_dyadic_bound_f 191142506804 137438953472 4 3 137438953472
  68719476736 p13604 p2504 p13605
  p13606 p2507

noncomputable def p13608 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 191142506804) (BSN.sinEvenQ 137438953472) 0
  3 p13604 p2504 p13605 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p13609 :=
p13607 p13605 135217178940 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p13608 (Eq.refl true))

noncomputable def p13610 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 191142506804) (BSN.sinOddQ 137438953472) 0
  3 p13606 p2507 p13605 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p13611 :=
p13596 d93 d95 d97 d99 d103
  (p13602 (p13603 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p13609 (p13610 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p13612 :=
p13532 BSN.abs_quadSignPos (BSN.cos_quad_nat3 279 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 122423913563 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101532600 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p13611 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p13544 846730078374775459 p3054 284973530396075
    137438953472 3364 137438953472
    (@p13548 p13542 p13543 846730078374775459
      p3054
      (p13550 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p13553 (p13584 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p13546 p13547)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p13613 :=
nat_lit
  10957707231825156577043090171791122192774291779516391324751113085395630154334093955635352428702667239731168094557229096003338410407689632785361

noncomputable def p13614 :=
nat_lit
  4541789819512410268201891400660389706164296124440801573357475913499233852341517573791049400223736100902580603721895350042028566664618961

noncomputable def p13615 :=
nat_lit
  54736614780692891917124856389410572788725406140586337067718364716663427244146153426863278930566845957582133860575938657181727563403963852039121

noncomputable def p13616 :=
BSN.sin_dyadic_bound_f 201729271131 137438953472 4 3 137438953472
  68719476736 p13613 p2504 p13614
  p13615 p2507

noncomputable def p13617 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 201729271131) (BSN.sinEvenQ 137438953472) 0
  3 p13613 p2504 p13614 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p13618 :=
p13616 p13614 136710232031 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p13617 (Eq.refl true))

noncomputable def p13619 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 201729271131) (BSN.sinOddQ 137438953472) 0
  3 p13615 p2507 p13614 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p13620 :=
nat_lit
  3440408693119487461694582070797834637257364014057444371763671724857038124692457347960259169877973777020995677707359428980075532125165306049761

noncomputable def p13621 :=
nat_lit
  141015984508961825510481812141291939893486427079008428998812453147383747549372756183849070247875739794642456503439762494035606198875361

noncomputable def p13622 :=
nat_lit
  17196915604989134257895246685913479044464904000529835333173516149500458917126225996414065601317117163660572164612016234834965380181847959991521

noncomputable def p13623 :=
BSN.sin_dyadic_bound_f 151044771081 137438953472 4 3 137438953472
  68719476736 p13620 p2504 p13621
  p13622 p2507

noncomputable def p13624 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 151044771081) (BSN.sinEvenQ 137438953472) 0
  3 p13620 p2504 p13621 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p13625 :=
p13623 p13621 122423913563 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p13624 (Eq.refl true))

noncomputable def p13626 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 151044771081) (BSN.sinOddQ 137438953472) 0
  3 p13622 p2507 p13621 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p13627 :=
p13612 d105 d107 d109 d111 d103
  (p13618 (p13619 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p13625 (p13626 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p13628 :=
p13527 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 62 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 129898389260 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101532600 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p13627 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p13544 846730078374775459 p3054 284973530396075
    137438953472 3364 137438953472
    (@p13548 p13542 p13543 846730078374775459
      p3054
      (p13550 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p13553 (p13584 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p13546 p13547)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p13629 :=
nat_lit
  7543798662898012509858987113814293291409677789292737847058690654820002317857938882567831620375688769011412174472653898188958068808809727359281

noncomputable def p13630 :=
nat_lit
  1484089348738439461057987353010046647424685416888136493772632584303123459722704158280751694922090712635049812165070906373757338613938481

noncomputable def p13631 :=
nat_lit
  37694363890120076681945477588013948802828370576170801304339629486422673221239332482546753499967270007069022071442725677010933843330073547995441

noncomputable def p13632 :=
BSN.sin_dyadic_bound_f 183775806509 137438953472 4 3 137438953472
  68719476736 p13629 p2504 p13630
  p13631 p2507

noncomputable def p13633 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 183775806509) (BSN.sinEvenQ 137438953472) 0
  3 p13629 p2504 p13630 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p13634 :=
p13632 p13630 133704390888 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p13633 (Eq.refl true))

noncomputable def p13635 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 183775806509) (BSN.sinOddQ 137438953472) 0
  3 p13631 p2507 p13630 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p13636 :=
nat_lit 2623389544392391652819988688179367378206032837289124597990549559433233518345367614757339136

noncomputable def p13637 :=
nat_lit 19152344519746593640524221023248538169493031511136432768957877279599576328267177721856

noncomputable def p13638 :=
nat_lit 7870130328488135465272685016096055637541759525804351521106110762545141355883446309916573696

noncomputable def p13639 :=
BSN.cos_dyadic_bound_f 45738060348 137438953472 3 2 137438953472
  68719476736 p13636 p2466 p13637
  p13638 p2469

noncomputable def p13640 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP 45738060348) (BSN.cosEvenQ 137438953472) 0
  2 p13636 p2466 p13637 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p13641 :=
p13639 p13637 129898389260 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p13640 (Eq.refl true))

noncomputable def p13642 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP 45738060348) (BSN.cosOddQ 137438953472) 0
  2 p13638 p2469 p13637 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p13643 :=
p13628 d113 d115 d117 d119 d103
  (p13634 (p13635 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p13641 (p13642 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p13644 :=
p13522 BSN.abs_quadSignPos (BSN.cos_quad_nat0 100 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 128420273409 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101532600 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p13643 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p13544 846730078374775459 p3054 284973530396075
    137438953472 3364 137438953472
    (@p13548 p13542 p13543 846730078374775459
      p3054
      (p13550 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p13553 (p13584 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p13546 p13547)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p13645 :=
nat_lit 128708010189211825217156912511360519971046468504660815162543204756099630422574507376050176

noncomputable def p13646 :=
nat_lit 46101341314205310116262239166947712821044349798454688187301541715034184760961335296

noncomputable def p13647 :=
nat_lit 386123938364952847240850505009603226017713763425282848578253239665215461199354000205479936

noncomputable def p13648 :=
BSN.cos_dyadic_bound_f 21526042588 137438953472 3 2 137438953472
  68719476736 p13645 p2466 p13646
  p13647 p2469

noncomputable def p13649 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP 21526042588) (BSN.cosEvenQ 137438953472) 0
  2 p13645 p2466 p13646 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p13650 :=
p13648 p13646 135756664568 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p13649 (Eq.refl true))

noncomputable def p13651 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP 21526042588) (BSN.cosOddQ 137438953472) 0
  2 p13647 p2469 p13646 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p13652 :=
nat_lit 3766470902575086855012085189545994218828653563994737454840284909618880604227873095185157441

noncomputable def p13653 :=
nat_lit 39478700531153009479883711858789964185903611360876356314007752287367866616191829232961

noncomputable def p13654 :=
nat_lit 11299333750324198259017295801214265076557588884761490611808226713352067076950386901897006401

noncomputable def p13655 :=
BSN.cos_dyadic_bound_f 50066283721 137438953472 3 2 137438953472
  68719476736 p13652 p2466 p13653
  p13654 p2469

noncomputable def p13656 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP 50066283721) (BSN.cosEvenQ 137438953472) 0
  2 p13652 p2466 p13653 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p13657 :=
p13655 p13653 128420273409 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p13656 (Eq.refl true))

noncomputable def p13658 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP 50066283721) (BSN.cosOddQ 137438953472) 0
  2 p13654 p2469 p13653 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p13659 :=
p13644 d121 d123 d125 d127 d103
  (p13650 (p13651 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p13657 (p13658 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p13660 :=
p13517 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 229 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 136844160670 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101532600 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p13659 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p13544 846730078374775459 p3054 284973530396075
    137438953472 3364 137438953472
    (@p13548 p13542 p13543 846730078374775459
      p3054
      (p13550 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p13553 (p13584 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p13546 p13547)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p13661 :=
nat_lit 16299368278138261529803144557670951810339803753698684796077806576200550594153883986257831201

noncomputable def p13662 :=
nat_lit 739273040175341949159271550878247435829896280413365199829132618337933781280702681900321

noncomputable def p13663 :=
nat_lit 48896626288334433905511115129911098936147751468535227657833761463364975914899090553409692961

noncomputable def p13664 :=
BSN.cos_dyadic_bound_f 72210542637 137438953472 3 2 137438953472
  68719476736 p13661 p2466 p13662
  p13663 p2469

noncomputable def p13665 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP 72210542637) (BSN.cosEvenQ 137438953472) 0
  2 p13661 p2466 p13662 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p13666 :=
p13664 p13662 118901594537 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p13665 (Eq.refl true))

noncomputable def p13667 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP 72210542637) (BSN.cosOddQ 137438953472) 0
  2 p13663 p2469 p13662 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p13668 :=
nat_lit
  11258491233182595949858763187537638771463832370420456984214974004619294331980366752475530889237476928996836982799559629574023661113021809388641

noncomputable def p13669 :=
nat_lit
  4925539286318302472607448623598925388128784882394992666261922850317953064654457002794788905572217215520672739851352856639059775177452641

noncomputable def p13670 :=
nat_lit
  56237649310895703748917594303060269452137264511921394297628282489057902831722647839616615077118524894409627813470160243204668258051608118652001

noncomputable def p13671 :=
BSN.sin_dyadic_bound_f 203097455447 137438953472 4 3 137438953472
  68719476736 p13668 p2504 p13669
  p13670 p2507

noncomputable def p13672 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 203097455447) (BSN.sinEvenQ 137438953472) 0
  3 p13668 p2504 p13669 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p13673 :=
p13671 p13669 136844160670 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p13672 (Eq.refl true))

noncomputable def p13674 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 203097455447) (BSN.sinOddQ 137438953472) 0
  3 p13670 p2507 p13669 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p13675 :=
p13660 d129 d131 d133 d135 d103
  (p13666 (p13667 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p13673 (p13674 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p13676 :=
p13512
  (p13675 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p13544 846730078374775459 p3054 284973530396075
    137438953472 3364 137438953472
    (@p13548 p13542 p13543 846730078374775459
      p3054
      (p13550 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p13553 (p13584 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p13546 p13547)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p13677 :=
nat_lit 1456253940938881102482114427259552230188019222438855055163605217636107687712451977176743936

noncomputable def p13678 :=
nat_lit 5901649692520585190609369595766692233242130030570341549413817360978304830242941894656

noncomputable def p13679 :=
nat_lit 4368750019517258266275962063039465157179591183056504024807716825273601106527695445646442496

noncomputable def p13680 :=
BSN.cos_dyadic_bound_f 39479503148 137438953472 3 2 137438953472
  68719476736 p13677 p2466 p13678
  p13679 p2469

noncomputable def p13681 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP 39479503148) (BSN.cosEvenQ 137438953472) 0
  2 p13677 p2466 p13678 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p13682 :=
p13680 p13678 131807568577 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p13681 (Eq.refl true))

noncomputable def p13683 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP 39479503148) (BSN.cosOddQ 137438953472) 0
  2 p13679 p2469 p13678 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p13684 :=
p13676 d137 d139 d103
  (p13682 (p13683 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true) (Eq.refl true)

noncomputable def p13685 :=
@p13501 p13485 p13487 p13488
  (p13505
    (@p13508 109059 34359738368
      (p13684 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (p13684 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true) (Eq.refl true)))

noncomputable def p13686 :=
@Enclosure.Real.IsNear.mulLit_ff p13492
  (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
        (Enclosure.sfrac false 12 1)))
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Zeta.RiemannSiegel.correctionLinear
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
          (Enclosure.sfrac false 12 1)))
      (@Inv.inv Real Real.instInv p13493)))

noncomputable def p13687 :=
nat_lit
  235375256618337097960780959737567943132722372234462096168487972458460405159877196282725591801149951462627203631592456225810166076718214564574990035647024811941594811290846248765

noncomputable def p13688 :=
nat_lit
  506532662216918085755909163048237445191949002959281848144001138878253517018177263964807989373425756138696031080481053366991595590260226478013534525648677207893210669360535830528

noncomputable def p13689 :=
nat_lit
  182415467675831272639082267934031241692583831319110788246324362881795746228677278065977987262275139899807919761637995160057228729059397642527212428795153056092508414446692782851665493799367238072298282090677488135868573916936893

noncomputable def p13690 :=
nat_lit
  981518579511447820674316499993658965762126974896466157216253315487651735821534006436781207997308165424048782178541711352749052991248548652928675275490386247680000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p13691 :=
@p13686 1204629381 4294967296 1 8589934592
  p13687 p13688 p13689 p13690
  p13498 p13485 p13499

noncomputable def p13692 :=
@Enclosure.Real.IsNear.mulLit_ff
  c22
  (p13491
    (@Neg.neg Real Real.instNeg
      (@HDiv.hDiv Real Real Real c4
        c38
        c20)))

noncomputable def p13693 :=
@p13692 1 1 0 1 1204629381 4294967296
  1 8589934592 1204629381 4294967296 1

noncomputable def p13694 :=
@Enclosure.Real.IsNear.of_eq
  (p13491
    (@Neg.neg Real Real.instNeg
      (@HDiv.hDiv Real Real Real c4
        c38
        c20)))

noncomputable def p13695 :=
BSN.rpow_neg_quarter_mk
  (@HDiv.hDiv Real Real Real c4
    (@OfScientific.ofScientific Real c2 101532600
      true 5)
    c7)

noncomputable def p13696 :=
p13695
  (BSN.t_div_two_pi_nonneg
    (@OfScientific.ofScientific Real c2 101532600
      true 5)
    101532600 100000
    (Enclosure.sfrac_ofScientific_eq 101532600 5 100000 (Eq.refl true)))

noncomputable def p13697 :=
@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt p13493)) false
  4818517524 17179869184 2 17179869184 1204629381 4294967296

noncomputable def p13698 :=
@Enclosure.Real.IsNear.recentre' (Real.sqrt p13493) false 61252844619
  17179869184 7 17179869184 61252844619 17179869184 7
  17179869184

noncomputable def p13699 :=
@Enclosure.Real.IsNear.sqrt_image
  (@HDiv.hDiv Real Real Real c4
    (@OfScientific.ofScientific Real c2 101532600
      true 5)
    c7)

noncomputable def p13700 :=
@Enclosure.Real.IsNear.of_eq
  (@HDiv.hDiv Real Real Real c4
    (@OfScientific.ofScientific Real c2 101532600
      true 5)
    c7)

noncomputable def p13701 :=
@p13700
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 101532600 100000)
    (@Inv.inv Real Real.instInv
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)))
  false 1388083194332289

noncomputable def p13702 :=
@p13701 8589934592000 507663 8589934592000
  (BSN.t_div_two_pi_mk
    (@OfScientific.ofScientific Real c2 101532600
      true 5)
    101532600 100000
    (Enclosure.sfrac_ofScientific_eq 101532600 5 100000 (Eq.refl true)))

noncomputable def p13703 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 101532600 100000)
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi))
  101532600 100000 0

noncomputable def p13704 :=
@p13703 1 2734261103 17179869184 1 17179869184
  1388083194332289 8589934592000 507663 8589934592000
  (Enclosure.Real.IsNear.const false 101532600 100000) d142

noncomputable def p13705 :=
@p13699 1388083194332289 8589934592000 507663 8589934592000
  109194980851 109194980892 8589934592
  (p13702 (p13704 (Eq.refl true))) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p13706 :=
@Enclosure.Real.IsNear.recentre' p13493 false 218389961743 17179869184
  41 17179869184 218389961743 17179869184 41 17179869184
  (p13705 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p13707 :=
@Enclosure.Real.IsNear.sqrt_image p13493 218389961743 17179869184 41
  17179869184 30626422306 30626422313 8589934592
  (p13706 (Eq.refl true)) (Eq.refl true) (Eq.refl true)

noncomputable def p13708 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt p13493) 61252844619 17179869184
  7 17179869184 2409258761 2409258763 8589934592
  (p13698
    (p13707 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p13709 :=
@p13694 (@Inv.inv Real Real.instInv (Real.sqrt p13493)) false
  1204629381 4294967296 1 8589934592 p13696
  (@p13697 1 8589934592
    (p13708 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p13710 :=
@Enclosure.Real.IsNear.addLit_ft_p
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
      (Enclosure.sfrac false 12 1)))
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Zeta.RiemannSiegel.correctionLinear
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
        (Enclosure.sfrac false 12 1)))
    (@Inv.inv Real Real.instInv p13493))
  34344004938426213945

noncomputable def p13711 :=
nat_lit 39631676720860364800000000

noncomputable def p13712 :=
nat_lit
  389388122485280307859250268587332928273953569359745066593929437546305721041959636160955368654831127719754320040840860061339962348417312076441428115099429615343162242808135875

noncomputable def p13713 :=
nat_lit
  479714256111838104497540329047382997422717369178161746485067963948094300997785037540090869140611872583100407779364463573724807728422565416628200258556127170908414446692782851665493799367238072298282090677488135868573916936893

noncomputable def p13714 :=
nat_lit
  17367628480488699114496049354324222100088678969320730802150110506187959066890429445157726183308949593098073393273083653509332506669121008236719049300138936810979191073008904858114729286654975016960

noncomputable def p13715 :=
@p13710 73786976294838206464 7346186933196396401 p13711
  p13712 p13688 p13713 p13690
  p13714 p13687 p13688 p13689

noncomputable def p13716 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  (@Inv.inv Real Real.instInv
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
          (Enclosure.sfrac false 12 1)))))

noncomputable def p13717 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
        (Enclosure.sfrac false 12 1))
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
        (Enclosure.sfrac false 12 1)))
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
      (Enclosure.sfrac false 12 1)))

noncomputable def p13718 :=
@Enclosure.Real.IsNear.of_eq
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
      (Enclosure.sfrac false 12 1)))
  (p13716
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p13717 (Enclosure.sfrac false 1 16)))))

noncomputable def p13719 :=
BSN.cos_two_pi_p_ne_zero_mk
  (@OfScientific.ofScientific Real c2 101532600
    true 5)
  101532600 100000 12
  (Enclosure.sfrac_ofScientific_eq 101532600 5 100000 (Eq.refl true))

noncomputable def p13720 :=
@Enclosure.Real.IsNear.mulLit_tt
  (@Inv.inv Real Real.instInv
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
          (Enclosure.sfrac false 12 1)))))

noncomputable def p13721 :=
@p13720
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p13717 (Enclosure.sfrac false 1 16))))
  72584078915

noncomputable def p13722 :=
@p13721 17179869184 4699 17179869184 473161683
  4294967296 4068320057 110729625600000000 34344004938426213945
  73786976294838206464 7346186933196396401 p13711

noncomputable def p13723 :=
@Enclosure.Real.IsNear.of_eq
  (@Inv.inv Real Real.instInv
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
          (Enclosure.sfrac false 12 1)))))

noncomputable def p13724 :=
@Inv.inv Real Real.instInv
  (@Neg.neg Real Real.instNeg
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
          (Enclosure.sfrac false 12 1)))))

noncomputable def p13725 :=
@p13723 (@Neg.neg Real Real.instNeg p13724) true 72584078915
  17179869184 4699 17179869184
  (BSN.inv_eq_neg_inv_neg
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
          (Enclosure.sfrac false 12 1)))))

noncomputable def p13726 :=
@Enclosure.Real.IsNear.inv_image
  (@Neg.neg Real Real.instNeg
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
          (Enclosure.sfrac false 12 1)))))

noncomputable def p13727 :=
@Enclosure.Real.IsNear.neg
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
        (Enclosure.sfrac false 12 1))))
  true

noncomputable def p13728 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
        (Enclosure.sfrac false 12 1))))
  true

noncomputable def p13729 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
      (Enclosure.sfrac false 12 1)))
  (@HDiv.hDiv Real Real Real c4
    (@Nat.cast Real Real.instNatCast 76852979225)
    (@Nat.cast Real Real.instNatCast 17179869184))
  false

noncomputable def p13730 :=
nat_lit 10816095268752921759606925

noncomputable def p13731 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
      (Enclosure.sfrac false 12 1)))
  false p13730

noncomputable def p13732 :=
nat_lit 1106429196838861709297286367

noncomputable def p13733 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
    (Enclosure.sfrac false 12 1))
  884279719003555 140737488355328 1

noncomputable def p13734 :=
@Enclosure.Real.IsNear.subLit_ff_p p13493 (Enclosure.sfrac false 12 1)
  218389961743 17179869184 41 17179869184 12 1 0

noncomputable def p13735 :=
@p13733 500000000000000 12231531535 17179869184 41
  17179869184 p13730 p2602 p13732
  p5018 d141
  (@p13734 1 12231531535 12231531535 17179869184 41
    17179869184 (p13706 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p13736 :=
@p13729 76852979225 17179869184 129 8589934592 true
  4066289875 17179869184 1 3300000000
  (@p13731 p2602 p13732 p5018
    76852979225 17179869184 129 8589934592
    (p13735 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div 76852979225 17179869184)

noncomputable def p13737 :=
nat_lit 3297474889193497944664309760

noncomputable def p13738 :=
BSN.cos_reduce2
  (@HDiv.hDiv Real Real Real c4
    (@Nat.cast Real Real.instNatCast 76852979225)
    (@Nat.cast Real Real.instNatCast 17179869184))
  (@HDiv.hDiv Real Real Real c4
    (@Nat.cast Real Real.instNatCast p13737)
    (@Nat.cast Real Real.instNatCast p2333))
  226375608064910080 72057594037927936 false

noncomputable def p13739 :=
BSN.sin_reduce_arg_pos_rat_q2 76852979225 17179869184 226375608064910080
  72057594037927936 0 p13737 p2333 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p13740 :=
nat_lit
  226435106721915640634778424432144625232537455049005515374373607472272897813726699590954752651288641253814394363955209054224132364830769612277282434716186854245357713140625

noncomputable def p13741 :=
nat_lit
  112103806036672228432223676208184367293620745996950753450487220298901161785314500686292286189166059761431485632259878790410828018266721706021591489799163828369140625

noncomputable def p13742 :=
nat_lit
  1371993807828683118537071562224180548133652634524804087731220788833945209046694754758536350231371298606082026854750020925078945368989814750401639946657520526131130922740625

noncomputable def p13743 :=
BSN.cos_dyadic_bound_f 46859936577355 35184372088832 4 3 17179869184
  6606445313 p13740 p2613 p13741
  p13742 p2616

noncomputable def p13744 :=
@BSN.binarySplit_of_base3 (BSN.cosEvenP 46859936577355) (BSN.cosEvenQ 35184372088832) 0
  3 p13740 p2613 p13741 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p13745 :=
p13743 p13741 4066289875 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p13744 (Eq.refl true))

noncomputable def p13746 :=
@BSN.binarySplit_of_base3 (BSN.cosOddP 46859936577355) (BSN.cosOddQ 35184372088832) 0
  3 p13742 p2616 p13741 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p13747 :=
@BSN.cos_arg_round false 4066289875 17179869184 p13737
  p2333 46859936577355 35184372088832 6606445313 6600000000
  (p13745 (p13746 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p13748 :=
p13738 4066289875 17179869184 0 1000000000000000
  6600000000 3300000000 p13739 BSN.pi_near_15 p13747
  (Eq.refl true) (Eq.refl true)

noncomputable def p13749 :=
@p13727 4066289875 17179869184 1696445057 110729625600000000
  (@p13728 4066289875 17179869184 434289934592
    28346784153600000000 4066289875 17179869184 1696445057
    110729625600000000
    (p13736 (p13748 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p13750 :=
@p13726 4066289875 17179869184 1696445057 110729625600000000
  36292037108 36292041807 8589934592 p13749
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p13751 :=
@Enclosure.Real.IsNear.recentre' p13724 false 72584078915 17179869184
  4699 17179869184 72584078915 17179869184 4699 17179869184
  (p13750 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p13752 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p13717 (Enclosure.sfrac false 1 16))))
  true

noncomputable def p13753 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p13717 (Enclosure.sfrac false 1 16)))
  (@HDiv.hDiv Real Real Real c4
    (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 7220642901))
    (@Nat.cast Real Real.instNatCast 4294967296))
  true

noncomputable def p13754 :=
nat_lit 69833773099571231787608787778614205

noncomputable def p13755 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p13717 (Enclosure.sfrac false 1 16)))
  true p13754

noncomputable def p13756 :=
nat_lit 46074952436198551714783306840094009817

noncomputable def p13757 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (p13717 (Enclosure.sfrac false 1 16)) 884279719003555
  140737488355328 1

noncomputable def p13758 :=
@Enclosure.Real.IsNear.subLit_tf
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
        (Enclosure.sfrac false 12 1))
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
        (Enclosure.sfrac false 12 1)))
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
      (Enclosure.sfrac false 12 1)))

noncomputable def p13759 :=
@p13758 (Enclosure.sfrac false 1 16) 60525747999571261215
  295147905179352825856 1707360224095 295147905179352825856 1 16
  0

noncomputable def p13760 :=
@Enclosure.Real.IsNear.subLit_ff_n
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
      (Enclosure.sfrac false 12 1))
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
      (Enclosure.sfrac false 12 1)))
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
    (Enclosure.sfrac false 12 1))
  149610363691699456225

noncomputable def p13761 :=
nat_lit 1039824432896383955759592898560

noncomputable def p13762 :=
@p13760 295147905179352825856 1002985587551 295147905179352825856
  12231531535 17179869184 41 17179869184 p13761
  60525747999571261215 295147905179352825856 1707360224095

noncomputable def p13763 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
    (Enclosure.sfrac false 12 1))
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
    (Enclosure.sfrac false 12 1))
  12231531535 17179869184 41

noncomputable def p13764 :=
@p13763 17179869184 12231531535 17179869184 41
  17179869184 149610363691699456225 295147905179352825856 1002985587551
  295147905179352825856
  (@p13734 1 12231531535 12231531535 17179869184 41
    17179869184 (p13706 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p13765 :=
p13764
  (@p13734 1 12231531535 12231531535 17179869184 41
    17179869184 (p13706 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p13766 :=
@p13762 295147905179352825856 (p13765 (Eq.refl true))
  (@p13734 1 12231531535 12231531535 17179869184 41
    17179869184 (p13706 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p13767 :=
@p13757 500000000000000 78972492073280812831 295147905179352825856
  1707360224095 295147905179352825856 p13754 p2630
  p13756 p2632 d141
  (@p13759 1 1263559873172493005296 78972492073280812831
    295147905179352825856 1707360224095 295147905179352825856
    (p13766 (Eq.refl true) (Eq.refl true))
    (Enclosure.Real.IsNear.const false 1 16) (Eq.refl true)
    (Eq.refl true))

noncomputable def p13768 :=
@p13753 7220642901 4294967296 313 8589934592 true
  946323366 8589934592 1 3300000000
  (@p13755 p2630 p13756 p2632
    7220642901 4294967296 313 8589934592
    (p13767 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_true_div 7220642901 4294967296)

noncomputable def p13769 :=
nat_lit
  93819202045890067056401284237139003581583387681161405759724506686212590480407355674411111687153105302310570892403263714796438955731074024277438465330197079968008562881

noncomputable def p13770 :=
nat_lit
  54602669771916359224996195552921087953565327116081450193839337072628553298441183792728043047902785698785004776906248719566767110034517758778974860385819486401

noncomputable def p13771 :=
nat_lit
  953934103611917826446532295862903118850866766668987603144494416600001979793857615545988735217115057823689983962761151717624416198134885883712998497080623121501572753601

noncomputable def p13772 :=
BSN.cos_dyadic_bound_t 7220642901 4294967296 5 4 8589934592
  3300000000 p13769 p7870 p13770
  p13771 p7873

noncomputable def p13773 :=
@BSN.binarySplit_of_base4 (BSN.cosEvenP 7220642901) (BSN.cosEvenQ 4294967296) 0
  4 p13769 p7870 p13770 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p13774 :=
p13772 p13770 946323366 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p13773 (Eq.refl true))

noncomputable def p13775 :=
@BSN.binarySplit_of_base4 (BSN.cosOddP 7220642901) (BSN.cosOddQ 4294967296) 0 4
  p13771 p7873 p13770 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p13776 :=
p13768
  (BSN.cos_neg_of_bound 7220642901 4294967296 true 946323366 8589934592
    1 3300000000
    (p13774 (p13775 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p13777 :=
p13722
  (p13725
    (@Enclosure.Real.IsNear.neg p13724 false 72584078915 17179869184
      4699 17179869184 (p13751 (Eq.refl true))))
  (@p13752 946323366 8589934592 1041489934592
    28346784153600000000 473161683 4294967296 4068320057
    110729625600000000 (p13776 (Eq.refl true)) (Eq.refl true))

noncomputable def p13778 :=
@p13715 p13690
  (@p13718 false 34344004938426213945 73786976294838206464
    7346186933196396401 p13711
    (BSN.correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
        (Enclosure.sfrac false 12 1))
      (p13719 (Eq.refl true) (Eq.refl true)
        (p13496 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p13777 (Eq.refl true)))

noncomputable def p13779 :=
nat_lit
  288121500157377894221487249530922689970815272221308818898036652129338603338888589503267051299709692100202992110249697209096076058755158568217544112175184138501866625

noncomputable def p13780 :=
nat_lit
  29484081443918291814387145163970850710288447034503440846689111720668938768688662906922865040450459121417721679927842538279457692421287442441886205089317937841010900992

noncomputable def p13781 :=
@Enclosure.Real.IsNear.mulLit_tf
  (Zeta.RiemannSiegel.correctionLinear
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
      (Enclosure.sfrac false 12 1)))
  (@Inv.inv Real Real.instInv p13493) p13779 p13780

noncomputable def p13782 :=
nat_lit
  1772718852218245752049099046760506696585491882781418986282178867595610012749201094210390332447159948134499098060631005303982527621992245178101952153258363863401757502587475166360133783905142382096563877147420354966011

noncomputable def p13783 :=
nat_lit
  285659503282352764122862281508760924265407658792236516373305731536719172675376177776133760343453662185943913115928214786326586324502873657308715417600000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p13784 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  (@iteratedDeriv Real c11 Real
    Real.normedAddCommGroup
    c8
    (@OfNat.ofNat Nat 3 (instOfNatNat 3)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
      (Enclosure.sfrac false 12 1)))
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 96 1)
      c16))

noncomputable def p13785 :=
@Enclosure.Real.IsNear.of_eq
  (Zeta.RiemannSiegel.correctionLinear
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
      (Enclosure.sfrac false 12 1)))
  (@Neg.neg Real Real.instNeg p13784) true p13779

noncomputable def p13786 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@iteratedDeriv Real c11 Real
    Real.normedAddCommGroup
    c8
    (@OfNat.ofNat Nat 3 (instOfNatNat 3)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
      (Enclosure.sfrac false 12 1)))
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 96 1)
      c16))

noncomputable def p13787 :=
nat_lit
  3879420400130527024928320562769055182372273562041578346905308573740268206564928402571933816028832039827003507316693492340876384971828533099709678995601125

noncomputable def p13788 :=
nat_lit
  418993997810706159361688281193932691483730181893512293053861295116305125939798343025058571817715732115313495568327689089179808837873330310826051531440128

noncomputable def p13789 :=
nat_lit
  644444612051746881017394168919852932795525352257833003744525925085257022203992581549595066430438835233668734635055324076630788186315246061059816845028015838913545187632027399090478923389126590628743277076669

noncomputable def p13790 :=
nat_lit
  109605573877381695969536417589104998955434763095558792288091677157402410532471844816706316255380910419894542743151956176899628740693196800000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p13791 :=
@p13786 p13787 p13788 p13789
  p13790 74269213037 70368744177664 1 70368744177664
  p13779 p13780 p13782

noncomputable def p13792 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p13793 :=
p13792
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p13794 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p13793
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p13795 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p13794
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p13717 (Enclosure.sfrac false 1 16)))))

noncomputable def p13796 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  (Enclosure.sfrac false 3 1)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p13797 :=
p13795
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p13796
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 4 1) Real.pi))
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p13717 (Enclosure.sfrac false 1 16)))))

noncomputable def p13798 :=
@Neg.neg Real Real.instNeg
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
          (Enclosure.sfrac false 12 1)))))

noncomputable def p13799 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13797
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 3 1) p13798)
    (@iteratedDeriv Real c11 Real
      Real.normedAddCommGroup
      c10
      (@OfNat.ofNat Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
        (Enclosure.sfrac false 12 1))))

noncomputable def p13800 :=
@Neg.neg Real Real.instNeg
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 4 1)
      c16)
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
          (Enclosure.sfrac false 12 1)))))

noncomputable def p13801 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13799
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 3 1) p13800)
    (@iteratedDeriv Real c11 Real
      Real.normedAddCommGroup
      c10
      (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
        (Enclosure.sfrac false 12 1))))

noncomputable def p13802 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 8 1)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      c16 Real.pi))
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
        (Enclosure.sfrac false 12 1))))

noncomputable def p13803 :=
@Enclosure.Real.IsNear.of_eq
  (@iteratedDeriv Real c11 Real
    Real.normedAddCommGroup
    c8
    (@OfNat.ofNat Nat 3 (instOfNatNat 3)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
      (Enclosure.sfrac false 12 1)))
  (p13716
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13801
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p13802
        (Zeta.RiemannSiegel.correction
          (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
            (Enclosure.sfrac false 12 1))))))

noncomputable def p13804 :=
@p13720
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13801
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p13802
      (Zeta.RiemannSiegel.correction
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
          (Enclosure.sfrac false 12 1)))))
  297304375015245

noncomputable def p13805 :=
nat_lit
  13048648880231245748567256103554303104599749705035303172555215095219045977504750969927280375515128731295243703723154097808405613777931756025

noncomputable def p13806 :=
nat_lit
  5954262829429611647380060634218533145425030026750509549825967711687797048224955787888157087447151129073766576998532529631515456541611261952

noncomputable def p13807 :=
nat_lit
  2167571569984654090982515599332414002914569188233579381324829389981978420594485641270976421942756859066813978033429110015760513721386333169856858410832297555440069068700780007461181795769785137

noncomputable def p13808 :=
nat_lit
  1557588886347811239396839050486747154244465649178988432596663602075216353632524783516633935041979134722034569096421651251200000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p13809 :=
@p13804 70368744177664 4717 70368744177664 p13805
  p13806 p13807 p13808 p13787
  p13788 p13789 p13790

noncomputable def p13810 :=
@p13723 (@Neg.neg Real Real.instNeg p13724) true 297304375015245
  70368744177664 4717 70368744177664
  (BSN.inv_eq_neg_inv_neg
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
          (Enclosure.sfrac false 12 1)))))

noncomputable def p13811 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
      (Enclosure.sfrac false 12 1)))
  (@HDiv.hDiv Real Real Real c4
    c59
    c35)
  false

noncomputable def p13812 :=
nat_lit 44302726121791208873050879455

noncomputable def p13813 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
      (Enclosure.sfrac false 12 1)))
  false p13812

noncomputable def p13814 :=
nat_lit 1106859450526587693805567199

noncomputable def p13815 :=
@Enclosure.Real.IsNear.subLit_ff_p p13493 (Enclosure.sfrac false 12 1)
  894525283187349 70368744177664 41 70368744177664 12 1
  0

noncomputable def p13816 :=
@p13700
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 101532600 100000)
    (@Inv.inv Real Real.instInv
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)))
  false 1137117752508353967

noncomputable def p13817 :=
@p13816 7036874417766400 507663 35184372088832000
  (BSN.t_div_two_pi_mk
    (@OfScientific.ofScientific Real c2 101532600
      true 5)
    101532600 100000
    (Enclosure.sfrac_ofScientific_eq 101532600 5 100000 (Eq.refl true)))

noncomputable def p13818 :=
@p13703 1 11199533475045 70368744177664 1
  70368744177664 1137117752508353967 7036874417766400 507663
  35184372088832000 (Enclosure.Real.IsNear.const false 101532600 100000)
  d198

noncomputable def p13819 :=
@p13699 1137117752508353967 7036874417766400 507663
  35184372088832000 447262641593654 447262641593695 35184372088832
  (p13817 (p13818 (Eq.refl true))) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p13820 :=
@Enclosure.Real.IsNear.recentre' p13493 false 894525283187349 70368744177664
  41 70368744177664 894525283187349 70368744177664 41
  70368744177664
  (p13819 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p13821 :=
@p13733 500000000000000 50100353055381 70368744177664 41
  70368744177664 p13812 p12189 p13814
  p12191 d197
  (@p13815 1 50100353055381 50100353055381 70368744177664
    41 70368744177664 (p13820 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p13822 :=
@p13811 314789802202079 70368744177664 259 70368744177664
  true 16655524012681 70368744177664 1 13516800000000
  (@p13813 p12189 p13814 p12191
    314789802202079 70368744177664 259 70368744177664
    (p13821 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div 314789802202079 70368744177664)

noncomputable def p13823 :=
nat_lit 13506457044748506351030813851648

noncomputable def p13824 :=
BSN.cos_reduce2
  (@HDiv.hDiv Real Real Real c4
    c59
    c35)
  (@HDiv.hDiv Real Real Real c4
    (@Nat.cast Real Real.instNatCast p13823)
    (@Nat.cast Real Real.instNatCast p12201))
  226375608064910080 72057594037927936 false

noncomputable def p13825 :=
BSN.sin_reduce_arg_pos_rat_q2 314789802202079 70368744177664 226375608064910080
  72057594037927936 0 p13823 p12201
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p13826 :=
nat_lit
  95144735872894872893402645241647690781697400196607046547879132902919946753224931038810451890563937551752200542292650474182901753948445162672740414540753697165105728832660818965403576261624870222460302173846623366192289824167590095413781570271069719670465586097852855512950701690198163456

noncomputable def p13827 :=
nat_lit
  3393018743556686121335305039608970277666143417154295147228971930527908230070285730106240720351269169476096916927360415823939650619361122253095479430021982983648660501283872934042087247223354857365749991090118440992158300130799353828124285118510176621118391312070621313919614976

noncomputable def p13828 :=
nat_lit
  969266479066074313506089904354462544115380182674622874125669087656393346756712273571423198271794103340593548761624529092842924968209783258525252895848468737632088192648246007094349241102564983728308597209196002641913924878804109932473622919111509533574959533399632103693446667729608114176

noncomputable def p13829 :=
BSN.cos_dyadic_bound_f 191938298780037632 144115188075855872 5 4
  70368744177664 27060000000001 p13826 p12205
  p13827 p13828 p12208

noncomputable def p13830 :=
@BSN.binarySplit_of_base4 (BSN.cosEvenP 191938298780037632) (BSN.cosEvenQ 144115188075855872)
  0 4 p13826 p12205 p13827
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p13831 :=
p13829 p13827 16655524012681 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p13830 (Eq.refl true))

noncomputable def p13832 :=
@BSN.binarySplit_of_base4 (BSN.cosOddP 191938298780037632) (BSN.cosOddQ 144115188075855872)
  0 4 p13828 p12208 p13827
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p13833 :=
@BSN.cos_arg_round false 16655524012681 70368744177664 p13823
  p12201 191938298780037632 144115188075855872 27060000000001
  27033600000000
  (p13831 (p13832 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p13834 :=
p13824 16655524012681 70368744177664 0 1000000000000000
  27033600000000 13516800000000 p13825 BSN.pi_near_15 p13833
  (Eq.refl true) (Eq.refl true)

noncomputable def p13835 :=
@p13727 16655524012681 70368744177664 3405780739
  907097092915200000000
  (@p13728 16655524012681 70368744177664 3571219944177664
    p4996 16655524012681 70368744177664 3405780739
    907097092915200000000
    (p13822 (p13834 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p13836 :=
@p13726 16655524012681 70368744177664 3405780739
  907097092915200000000 148652187505264 148652187509981 35184372088832
  p13835 (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p13837 :=
@Enclosure.Real.IsNear.recentre' p13724 false 297304375015245 70368744177664
  4717 70368744177664 297304375015245 70368744177664 4717
  70368744177664
  (p13836 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p13838 :=
nat_lit
  680961520402016247198209520346661659330841132553901692027585254107122909217190308735465357854504375692722374026501628526616867495702580716025

noncomputable def p13839 :=
@Enclosure.Real.IsNear.subLit_tt_n p13801
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p13802
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
        (Enclosure.sfrac false 12 1))))
  p13838 p13806

noncomputable def p13840 :=
nat_lit
  2149897996878419706932855427369188881902130044119878675590174676118128437480954403857085718158248368447546967947431014492173362645501693644837200616496798328629377233887356719141181795769785137

noncomputable def p13841 :=
nat_lit 54479185559685351771161949847531316582763321807363111156003934445725031707731411916875

noncomputable def p13842 :=
nat_lit 485667223056432267729865476705879726660601709763034880312953102434726071301302124544

noncomputable def p13843 :=
nat_lit
  26026061983238440313311229921214137151469948464861773845513609012295762937186349516682329544251559968155286640473879123913

noncomputable def p13844 :=
nat_lit
  2293701712541175526280654642950342015905535177823959643118893090734080000000000000000000000000000000000000000000000000000000000000

noncomputable def p13845 :=
nat_lit
  6337301066300333567659434517706402955623210067587424663776929617171532151339032502492278238915429776952680669758703655299881041701156108166622761582191153999870868627259019758975570859566329918726864045465984087577172377600

noncomputable def p13846 :=
@p13839 p13840 p13808 p13841
  p13842 p13843 p13844 p13845
  p13805 p13806 p13807 p13808

noncomputable def p13847 :=
@Enclosure.Real.IsNear.subLit_tf p13799
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 3 1) p13800)
    (@iteratedDeriv Real c11 Real
      Real.normedAddCommGroup
      c10
      (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
        (Enclosure.sfrac false 12 1))))

noncomputable def p13848 :=
nat_lit
  544201374435278436624026349243402332316817972493322860761554943975913655958563036269794841175861494298024974689625934210978298707537972716025

noncomputable def p13849 :=
nat_lit
  2089992227096749014452794193523321165432313725710057720511344946404174377067935970776044279954351456070415340220814255815694875238868838110721030816669566951484161778722520454811205578169785137

noncomputable def p13850 :=
nat_lit
  55236983063284989908863466575761762678051768977174423501580402253636409572204504989627067055864693318177016703125

noncomputable def p13851 :=
nat_lit 2404907604760405225358828131112281116032698930082119547604265954848982041717359046106827774346003151904701415424

noncomputable def p13852 :=
nat_lit
  1877003459979659786434094265121495803775080083865537816469109212633307759703895471249236777432053345565889855992776566227939079459136714849531052109568454509

noncomputable def p13853 :=
nat_lit
  48803307921021617654819421802911881982471079775448500692740652885632267179730020806741834334208000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p13854 :=
nat_lit
  1637649538964016708200503175296522448556172103219376986435226353029772206197568523326262629798192172618813958948776942812842750732567568407114579028629478411123586070004712726162865351886031014639366799784651269120033114432184446441669205892424898969600

noncomputable def p13855 :=
@p13847 p13848 p13806 p13849
  p13808 p13850 p13851 p13852
  p13853 p13854 p13838 p13806

noncomputable def p13856 :=
@Enclosure.Real.IsNear.subLit_tf p13797
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 3 1) p13798)
    (@iteratedDeriv Real c11 Real
      Real.normedAddCommGroup
      c10
      (@OfNat.ofNat Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
        (Enclosure.sfrac false 12 1))))

noncomputable def p13857 :=
nat_lit 8246532482936897079057441161603468994393415527580524007202986442423353017985143853727891109108225

noncomputable def p13858 :=
nat_lit
  119103096301764126471847010179071539542309220444423987374667383126645305376035533230018569474049149562769364153056015459241

noncomputable def p13859 :=
nat_lit
  94856879503209427290989350919117134113398771438092750061123652819282435801035571200000000000000000000000000000000000000000000000000

noncomputable def p13860 :=
nat_lit
  498225419516932980262605654063208120788457608210161389904692934237115297617887263383900290950935196492153192026941987987362995692911454085625

noncomputable def p13861 :=
nat_lit
  2088036505381035562646920970757388279731184028376727684874153896509869040394662779723856212679904911147818199189288175732429748974488572960011800185628489449135275762722520454811205578169785137

noncomputable def p13862 :=
nat_lit
  581203540362047859907332887837896158997411197566872035314750562890034664538686574769546955478470001802144457612818591664947311821229052592529110722800649094202284745187386217214357808763651460685582925506617779342568340916051981316915200

noncomputable def p13863 :=
@p13856 p13857 p12373 p13858
  p13859 p13860 p13806 p13861
  p13808 p13862 p13848 p13806

noncomputable def p13864 :=
@Enclosure.Real.IsNear.subLit_tt_n
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p13794
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p13717 (Enclosure.sfrac false 1 16)))))

noncomputable def p13865 :=
@p13864
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p13796
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 4 1) Real.pi))
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p13717 (Enclosure.sfrac false 1 16)))))

noncomputable def p13866 :=
nat_lit 20061467641269297578721205246109105167575043219203211258433828902435803540001625780072929237850625

noncomputable def p13867 :=
nat_lit
  30775627534916112906148970778889663296771054594959736837100486695993291422864044718674527494272889840539522233056015459241

noncomputable def p13868 :=
nat_lit 135628804042493806615715730840348275386752082665182965275

noncomputable def p13869 :=
nat_lit 830627524462895051461434101429068874122009168267604542772233864278791349

noncomputable def p13870 :=
nat_lit 892029807941224925661428730905934460239216640000000000000000000000000000000000000

noncomputable def p13871 :=
nat_lit
  101102194061652011777278485451017710306720737842598400418549467654641895122785930795233604055392201260326842012389042490701019818470966872014188235980800

noncomputable def p13872 :=
@p13865 p13866 p12373 p13867
  p13859 p13868 p8159 p13869
  p13870 p13871 p13857 p12373

noncomputable def p13873 :=
nat_lit 2294692283560813681924728436736540578553595411526276918978208295803737539316420777375

noncomputable def p13874 :=
@Enclosure.Real.IsNear.mulLit_ft p13794
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p13717 (Enclosure.sfrac false 1 16))))
  p13873

noncomputable def p13875 :=
nat_lit 4302969004651745793852570085930363443097839368728459663643335809311459404862049316753703990931361915841

noncomputable def p13876 :=
@p13874 p12222 p13875 p12257
  8742552448095 8796093022208 4068320057 453548546457600000000
  p13866 p12373 p13867 p13859

noncomputable def p13877 :=
@Enclosure.Real.IsNear.mulLit_ff p13793
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p13878 :=
nat_lit 173973447705878860074740007012636677884081444433804073025

noncomputable def p13879 :=
nat_lit 35633248202726202683000846412944095821792145760591758751798459411

noncomputable def p13880 :=
nat_lit 13189899457762324432067081695

noncomputable def p13881 :=
nat_lit 221311443814336807302378131

noncomputable def p13882 :=
@p13877 p13878 p12261 p13879
  p12263 p13880 p12265 p13881
  p12267 p13873 p12222 p13875

noncomputable def p13883 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p13884 :=
@p13883
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p13885 :=
@p13884 p13880 p12265 p13881
  p12267 p13880 p12265 p13881
  p12267 p13878 p12261 p13879

noncomputable def p13886 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
        (Enclosure.sfrac false 12 1)))
    (Enclosure.sfrac false 1 1))
  884279719003555

noncomputable def p13887 :=
@p13886 140737488355328 1 500000000000000 14915980966549
  35184372088832 41 35184372088832 p13880 p12265
  p13881 p12267

noncomputable def p13888 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
      (Enclosure.sfrac false 12 1)))
  (Enclosure.sfrac false 1 1) 50100353055381 35184372088832

noncomputable def p13889 :=
@p13888 41 35184372088832 1 1 0 1
  14915980966549 14915980966549 35184372088832 41 35184372088832

noncomputable def p13890 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 2 1)
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
    (Enclosure.sfrac false 12 1))
  2 1 0 1

noncomputable def p13891 :=
@p13890 50100353055381 70368744177664 41 70368744177664
  50100353055381 35184372088832 41 35184372088832
  (Enclosure.Real.IsNear.const false 2 1)
  (@p13815 1 50100353055381 50100353055381 70368744177664
    41 70368744177664 (p13820 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p13892 :=
@p13885 p12263
  (p13887 d197
    (p13889 (p13891 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (p13887 d197
    (p13889 (p13891 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))

noncomputable def p13893 :=
@p13882 p12257 (p13892 (Eq.refl true))
  (p13887 d197
    (p13889 (p13891 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p13894 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p13717 (Enclosure.sfrac false 1 16))))
  true

noncomputable def p13895 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p13717 (Enclosure.sfrac false 1 16)))
  (@HDiv.hDiv Real Real Real c4
    (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 118303013591111))
    c35)
  true

noncomputable def p13896 :=
nat_lit 1171616298340479576936558944566607458049845

noncomputable def p13897 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p13717 (Enclosure.sfrac false 1 16)))
  true p13896

noncomputable def p13898 :=
nat_lit 188734383102090818072964989514125500573517

noncomputable def p13899 :=
nat_lit 1324938560912273303366935879

noncomputable def p13900 :=
nat_lit 1015453551090928234642154823

noncomputable def p13901 :=
@p13758 (Enclosure.sfrac false 1 16) p13900
  p12265 6993347461827147 p12265 1 16 0

noncomputable def p13902 :=
nat_lit 21199016974596372853870974064

noncomputable def p13903 :=
nat_lit 2510045376273824302053055161

noncomputable def p13904 :=
@Enclosure.Real.IsNear.subLit_ff_n
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
      (Enclosure.sfrac false 12 1))
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
      (Enclosure.sfrac false 12 1)))
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
    (Enclosure.sfrac false 12 1))
  p13903

noncomputable def p13905 :=
nat_lit 71456191161017989366924398227516106473472

noncomputable def p13906 :=
@p13904 p12265 4108228950542923 p12265
  50100353055381 70368744177664 41 70368744177664 p13905
  p13900 p12265 6993347461827147

noncomputable def p13907 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
    (Enclosure.sfrac false 12 1))
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
    (Enclosure.sfrac false 12 1))
  50100353055381 70368744177664 41

noncomputable def p13908 :=
@p13907 70368744177664 50100353055381 70368744177664 41
  70368744177664 p13903 p12265 4108228950542923
  p12265
  (@p13815 1 50100353055381 50100353055381 70368744177664
    41 70368744177664 (p13820 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p13909 :=
p13908
  (@p13815 1 50100353055381 50100353055381 70368744177664
    41 70368744177664 (p13820 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p13910 :=
@p13906 p12265 (p13909 (Eq.refl true))
  (@p13815 1 50100353055381 50100353055381 70368744177664
    41 70368744177664 (p13820 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p13911 :=
@p13757 500000000000000 p13899 p12265
  6993347461827147 p12265 p13896 p12284
  p13898 p12286 d197
  (@p13901 1 p13902 p13899 p12265
    6993347461827147 p12265
    (p13910 (Eq.refl true) (Eq.refl true))
    (Enclosure.Real.IsNear.const false 1 16) (Eq.refl true)
    (Eq.refl true))

noncomputable def p13912 :=
@p13895 118303013591111 70368744177664 313 35184372088832
  true 34970209792380 35184372088832 1 13516800000000
  (@p13897 p12284 p13898 p12286
    118303013591111 70368744177664 313 35184372088832
    (p13911 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_true_div 118303013591111 70368744177664)

noncomputable def p13913 :=
nat_lit
  8581721159424380281500607452739609147736312867757684488212722323622748262703879725038798848714594894554388571431186461114168040276079381891280222216195585194849696353670472344937852771566807014788646885740369538159760453320144885406081

noncomputable def p13914 :=
nat_lit
  128571681520656566270773152087415857057820519437562406788479640249394172804539086482387659909380154151240772139389538335266398745677386539016204403650755503189213561342629942804858641488667129024241854508874083974828065932057201606656000

noncomputable def p13915 :=
nat_lit
  1472085124887333112179296504822963428314427265815403791594953647892194757977796057571586626241886281340683840961402077847669162031057869821586453481436478473265655330678544595612618255415637211342167645255925312665471645669761

noncomputable def p13916 :=
nat_lit
  69765844842878318591011809964738352604596425109832115498797590694321837432416668347707435464721055302752889065240523311607466755837866637737974373848704206381392091284138978934479051589166324703548163160151733604187498675813825349704065

noncomputable def p13917 :=
nat_lit
  7328585846677424277434069668982703852295769607941057186943339494215467849858727929496096614834668786620724011945203685110184728503611032723923651008093063681785172996529906739876942564854026354381785707005822786565199758127260491579392000

noncomputable def p13918 :=
BSN.sin_dyadic_bound_f 118303013591111 70368744177664 5 4
  35184372088832 13516800000000 p13913 p13914
  p13915 p13916 p13917

noncomputable def p13919 :=
@BSN.binarySplit_of_base4 (BSN.sinEvenP 118303013591111) (BSN.sinEvenQ 70368744177664) 0
  4 p13913 p13914 p13915 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p13920 :=
p13918 p13915 34970209792380 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p13919 (Eq.refl true))

noncomputable def p13921 :=
@BSN.binarySplit_of_base4 (BSN.sinOddP 118303013591111) (BSN.sinOddQ 70368744177664) 0
  4 p13916 p13917 p13915 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p13922 :=
p13912
  (BSN.sin_neg_of_bound 118303013591111 70368744177664 false 34970209792380
    35184372088832 1 13516800000000
    (p13920 (p13921 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p13923 :=
p13876 p13893
  (@p13894 34970209792380 35184372088832 4265942772088832
    p12185 8742552448095 8796093022208 4068320057
    453548546457600000000 (p13922 (Eq.refl true))
    (Eq.refl true))

noncomputable def p13924 :=
nat_lit 34990681758585632130442375961281926541277175

noncomputable def p13925 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p13796
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 4 1) Real.pi))
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p13717 (Enclosure.sfrac false 1 16))))
  p13924

noncomputable def p13926 :=
nat_lit 17919056526776395709455097393217327029044216591982031

noncomputable def p13927 :=
@p13925 p12314 p13926 p12316
  3876140653053 35184372088832 4068320057 453548546457600000000
  p13868 p8159 p13869 p13870

noncomputable def p13928 :=
nat_lit 39569698373286973296201245085

noncomputable def p13929 :=
nat_lit 663934331443010421907134393

noncomputable def p13930 :=
@Enclosure.Real.IsNear.mulLit_ff p13796
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 4 1) Real.pi)
  p13928 p12265 p13929 p12267

noncomputable def p13931 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 3 1)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p13932 :=
@p13931 3 1 0 1 p13880
  p12265 p13881 p12267 p13928
  p12265 p13929

noncomputable def p13933 :=
@p13932 p12267 (Enclosure.Real.IsNear.const false 3 1)
  (p13887 d197
    (p13889 (p13891 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p13934 :=
@p13930 884279719003555 70368744177664 1 250000000000000
  p13924 p12314 p13926 p12316
  p13933 d199 (Eq.refl true)

noncomputable def p13935 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p13717 (Enclosure.sfrac false 1 16)))
  (@HDiv.hDiv Real Real Real c4
    (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 118303013591111))
    c35)
  true

noncomputable def p13936 :=
@p13935 118303013591111 70368744177664 313 35184372088832
  true 3876140653053 35184372088832 1 13516800000000
  (@p13897 p12284 p13898 p12286
    118303013591111 70368744177664 313 35184372088832
    (p13911 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_true_div 118303013591111 70368744177664)

noncomputable def p13937 :=
nat_lit
  2529360709386677649608896872106065644840815072877687596422778221598407101469118015709007848057279216104110292022227476567205230244801408279656139875709092282510547001051416538549849692860733453236778654888838171527669878449452190816641

noncomputable def p13938 :=
nat_lit
  7563040089450386251221950122789168062224736437503670987557625897023186635561122734258097641728244361837692478787619902074494043863375678765659082567691500187600797726037055459109331852274537001425991441698475527931062701885717741568000

noncomputable def p13939 :=
nat_lit
  25718012819617332747526396403514347754858974126618513055078501381438670463263526911316869875867507167060183911019944788990047683454559731875338497327909206027739521719542296210565983129855553235971699095622912451273534815102436236876161

noncomputable def p13940 :=
nat_lit
  1157145133685909096436958368786742713520384674938061661096316762244547555240851778341488939184421387361166949254505845017397588711096478851145839632856799528702922052083669485243727773398004161218176690579866755773452593388514814459904000

noncomputable def p13941 :=
BSN.cos_dyadic_bound_t 118303013591111 70368744177664 5 4
  35184372088832 13516800000000 p13937 p13938
  p13915 p13939 p13940

noncomputable def p13942 :=
@BSN.binarySplit_of_base4 (BSN.cosEvenP 118303013591111) (BSN.cosEvenQ 70368744177664) 0
  4 p13937 p13938 p13915 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p13943 :=
p13941 p13915 3876140653053 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p13942 (Eq.refl true))

noncomputable def p13944 :=
@BSN.binarySplit_of_base4 (BSN.cosOddP 118303013591111) (BSN.cosOddQ 70368744177664) 0
  4 p13939 p13940 p13915 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p13945 :=
p13936
  (BSN.cos_neg_of_bound 118303013591111 70368744177664 true 3876140653053
    35184372088832 1 13516800000000
    (p13943 (p13944 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p13946 :=
p13927 p13934
  (@p13752 3876140653053 35184372088832 4265942772088832
    p12185 3876140653053 35184372088832 4068320057
    453548546457600000000 (p13945 (Eq.refl true))
    (Eq.refl true))

noncomputable def p13947 :=
nat_lit 181372610564874513735022412865

noncomputable def p13948 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 3 1) p13798)
  (@iteratedDeriv Real c11 Real
    Real.normedAddCommGroup
    c8
    (@OfNat.ofNat Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
      (Enclosure.sfrac false 12 1)))
  p13947

noncomputable def p13949 :=
nat_lit 91916226350237416751545989399126613

noncomputable def p13950 :=
nat_lit 1298650782789152433766400000000000000000000000

noncomputable def p13951 :=
nat_lit 2746971651150847443695490094495383240112592844798864601337600327569875292116125941285438806456579940950559133625

noncomputable def p13952 :=
nat_lit
  87772571269191928271026650282598917378402523444070154294257643037927489772308060531565496591419777203136851829141167544750719015521632659017035999

noncomputable def p13953 :=
nat_lit
  1199390095467027275484842110228362411601209256561422353024794285317298598209044991346487320597495808000000000000000000000000000000000000000000000000000000

noncomputable def p13954 :=
@p13948 p12189 p13949 p13950
  p13951 p12231 p13952 p13953
  p13860 p13806 p13861 p13808

noncomputable def p13955 :=
nat_lit 60457536854958171245007470955

noncomputable def p13956 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 3 1) p13798
  3 1 0 1 p13955 p12189

noncomputable def p13957 :=
nat_lit 3895952348367457301299200000000000000000000000

noncomputable def p13958 :=
@Enclosure.Real.IsNear.neg
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
          (Enclosure.sfrac false 12 1)))))

noncomputable def p13959 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
        (Enclosure.sfrac false 12 1))))
  884279719003555

noncomputable def p13960 :=
@p13959 140737488355328 1 500000000000000 68369245110681
  70368744177664 3405780739 907097092915200000000 p13955
  p12189 p13949 p13957

noncomputable def p13961 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
        (Enclosure.sfrac false 12 1))))
  true

noncomputable def p13962 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
      (Enclosure.sfrac false 12 1)))
  (@HDiv.hDiv Real Real Real c4
    c59
    c35)
  false

noncomputable def p13963 :=
@p13962 314789802202079 70368744177664 259 70368744177664
  true 68369245110681 70368744177664 1 13516800000000
  (@p13813 p12189 p13814 p12191
    314789802202079 70368744177664 259 70368744177664
    (p13821 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div 314789802202079 70368744177664)

noncomputable def p13964 :=
BSN.sin_reduce2
  (@HDiv.hDiv Real Real Real c4
    c59
    c35)
  (@HDiv.hDiv Real Real Real c4
    (@Nat.cast Real Real.instNatCast p13823)
    (@Nat.cast Real Real.instNatCast p12201))
  226375608064910080 72057594037927936 false

noncomputable def p13965 :=
nat_lit
  323223242171944953430560519528588361951255296368917003917159728717448943921846943964936629727048542968169481618228133364744552975355331311172136315305183583064284767438770443680976622509159452742160614885654079748791716553775358507023829538880864722711398982155411654340364895986904989696

noncomputable def p13966 :=
nat_lit
  2630269183454551875273692085854968528121428478544570572302383292072319186928744887051095236561513068510221571019145287393233832731921836276700431243131303172039205528177780533441751901500684222034467077180729902894991511787252640425346875497533084093598059099768555503689692410890325852160

noncomputable def p13967 :=
BSN.sin_dyadic_bound_f 191938298780037632 144115188075855872 5 4
  70368744177664 27060000000001 p13965 p12357
  p13827 p13966 p12359

noncomputable def p13968 :=
@BSN.binarySplit_of_base4 (BSN.sinEvenP 191938298780037632) (BSN.sinEvenQ 144115188075855872)
  0 4 p13965 p12357 p13827
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p13969 :=
p13967 p13827 68369245110681 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p13968 (Eq.refl true))

noncomputable def p13970 :=
@BSN.binarySplit_of_base4 (BSN.sinOddP 191938298780037632) (BSN.sinOddQ 144115188075855872)
  0 4 p13966 p12359 p13827
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p13971 :=
@BSN.sin_arg_round false 68369245110681 70368744177664 p13823
  p12201 191938298780037632 144115188075855872 27060000000001
  27033600000000
  (p13969 (p13970 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p13972 :=
p13964 68369245110681 70368744177664 0 1000000000000000
  27033600000000 13516800000000 p13825 BSN.pi_near_15 p13971
  (Eq.refl true) (Eq.refl true)

noncomputable def p13973 :=
p13960 d197
  (@p13961 68369245110681 70368744177664 3571219944177664
    p4996 68369245110681 70368744177664 3405780739
    907097092915200000000
    (p13963 (p13972 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p13974 :=
@Neg.neg Real Real.instNeg
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p13793
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p13717 (Enclosure.sfrac false 1 16)))))

noncomputable def p13975 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13974
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 4 1) Real.pi)
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p13717 (Enclosure.sfrac false 1 16)))))

noncomputable def p13976 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13975
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) p13798)
    (@iteratedDeriv Real c11 Real
      Real.normedAddCommGroup
      c10
      (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
        (Enclosure.sfrac false 12 1))))

noncomputable def p13977 :=
@Enclosure.Real.IsNear.of_eq
  (@iteratedDeriv Real c11 Real
    Real.normedAddCommGroup
    c8
    (@OfNat.ofNat Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
      (Enclosure.sfrac false 12 1)))
  (p13716
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13976
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p13800
        (Zeta.RiemannSiegel.correction
          (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
            (Enclosure.sfrac false 12 1))))))

noncomputable def p13978 :=
@p13720
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13976
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p13800
      (Zeta.RiemannSiegel.correction
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
          (Enclosure.sfrac false 12 1)))))
  297304375015245

noncomputable def p13979 :=
nat_lit 9239593769886466812584143465556260223147364238070775223298383548142173941855711001702711210474525

noncomputable def p13980 :=
nat_lit 8543948143683640329580086824678208458410818089426611079788166431288878903122562200091848347746304

noncomputable def p13981 :=
nat_lit
  294935542152529021860290915594211764438612285451031329353549445991898912900794437350421728619468337479230487256473034991587674747227

noncomputable def p13982 :=
nat_lit
  17044358393534185942781421519901562243166058245853695794733003556832764476909076611072000000000000000000000000000000000000000000000000000000

noncomputable def p13983 :=
@p13978 70368744177664 4717 70368744177664 p13979
  p13980 p13981 p13982 p13951
  p12231 p13952 p13953

noncomputable def p13984 :=
nat_lit 27919752370199045694931169523571153785411713450467960825327395943617002052748685953927994625557475

noncomputable def p13985 :=
@Enclosure.Real.IsNear.subLit_ff_n p13976
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p13800
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
        (Enclosure.sfrac false 12 1))))
  p13984 p13980

noncomputable def p13986 :=
nat_lit
  286547698757631434694516997272803394208065168785137478835860812213823306042454269280914293131574513586712833039215250968138074747227

noncomputable def p13987 :=
nat_lit 15008540381946249396432381620583009688603554413763064314691839912899625

noncomputable def p13988 :=
nat_lit 3450873173395281893717377931138512726225554486085193277581262111899648

noncomputable def p13989 :=
nat_lit 262812933234479293900527687548339932334629621270447707052223477248900457772227971748225291912639

noncomputable def p13990 :=
nat_lit 534044046080944949360716772021339744307458209298541686292480000000000000000000000000000000000000000000000

noncomputable def p13991 :=
nat_lit
  31884666273571387701841449150432729366310292369674492163191446858494005664673227694183127925643343863490810802450367877396391160481428186972360713652053448303260467200

noncomputable def p13992 :=
@p13985 p13986 p13982 p13987
  p13988 p13989 p13990 p13991
  p13979 p13980 p13981 p13982

noncomputable def p13993 :=
@Enclosure.Real.IsNear.subLit_ff_p p13975
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) p13798)
    (@iteratedDeriv Real c11 Real
      Real.normedAddCommGroup
      c10
      (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
        (Enclosure.sfrac false 12 1))))

noncomputable def p13994 :=
nat_lit 11449594282040751492415120211063406285224200944607868128388508902084925

noncomputable def p13995 :=
nat_lit 862718293348820473429344482784628181556388621521298319395315527974912

noncomputable def p13996 :=
nat_lit 74847587929056000593787158765203411289746913940134090631580291082129124905081152956427

noncomputable def p13997 :=
nat_lit 414288714535520930413162101931705983462755459334626277851136000000000000000000000000000000000000

noncomputable def p13998 :=
nat_lit 85471537192290500431484131534825527476781022579943296123203102350581841947028598085061206756228125

noncomputable def p13999 :=
nat_lit
  283468374921874346472117426377269694441796351192778304253100496154807216444423558133207789678967603871318603078511250968138074747227

noncomputable def p14000 :=
nat_lit
  24086881115539806011962911188181439355964657613548530393809100614353836458426114338676879510455492965089065914205452979647593187279852208519990991555794994805814067200

noncomputable def p14001 :=
@p13993 p13994 p13995 p13996
  p13997 p13998 p13980 p13999
  p13982 p14000 p13984 p13980

noncomputable def p14002 :=
@Enclosure.Real.IsNear.subLit_ft p13974
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 4 1) Real.pi)
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p13717 (Enclosure.sfrac false 1 16)))))

noncomputable def p14003 :=
nat_lit 674345553204547229357409939171147332237023852260684851444174801195325

noncomputable def p14004 :=
nat_lit 852948294086619853176056340957782844533096820327329922762295547013362146214580392619

noncomputable def p14005 :=
nat_lit 12554203470773361527671578846415332832204710888928069025792000000000000000000000000000000000000

noncomputable def p14006 :=
nat_lit 7730861822175288459257977725

noncomputable def p14007 :=
nat_lit 109791864084565833012816530770071119

noncomputable def p14008 :=
nat_lit 7086955597655596632900956316149792578887046001900703559283156143387427749986080252436825086361600

noncomputable def p14009 :=
@p14002 p14003 p13995 p14004
  p14005 p14006 p504 p14007
  p12402 p14008 p13994 p13995

noncomputable def p14010 :=
@Enclosure.Real.IsNear.neg
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p13793
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p13717 (Enclosure.sfrac false 1 16)))))

noncomputable def p14011 :=
@Enclosure.Real.IsNear.mulLit_ft p13793
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p13717 (Enclosure.sfrac false 1 16))))
  p13878

noncomputable def p14012 :=
@p14011 p12261 p13879 p12263
  3876140653053 35184372088832 4068320057 453548546457600000000
  p14003 p13995 p14004 p14005

noncomputable def p14013 :=
p14012 (p13892 (Eq.refl true))
  (@p13752 3876140653053 35184372088832 4265942772088832
    p12185 3876140653053 35184372088832 4068320057
    453548546457600000000 (p13945 (Eq.refl true))
    (Eq.refl true))

noncomputable def p14014 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 4 1) Real.pi)
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p13717 (Enclosure.sfrac false 1 16))))
  884279719003555

noncomputable def p14015 :=
@p14014 70368744177664 1 250000000000000 8742552448095
  8796093022208 4068320057 453548546457600000000 p14006
  p504 p14007 p12402

noncomputable def p14016 :=
p14015 d199
  (@p13894 34970209792380 35184372088832 4265942772088832
    p12185 8742552448095 8796093022208 4068320057
    453548546457600000000 (p13922 (Eq.refl true))
    (Eq.refl true))

noncomputable def p14017 :=
@p14001 p13986 p13982
  (@p14009 p13996 p13997
    (@p14010 true p14003 p13995 p14004
      p14005 (p14013 (Eq.refl true)))
    (p14016 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p14018 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1) p13798)
  (@iteratedDeriv Real c11 Real
    Real.normedAddCommGroup
    c8
    (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
      (Enclosure.sfrac false 12 1)))
  p13955

noncomputable def p14019 :=
nat_lit 1413744946264394674741721265912191700274553278637486774053020619764375

noncomputable def p14020 :=
nat_lit 11891027110777813783153401667425212528344719737945147508958849649519954435213494373429

noncomputable def p14021 :=
nat_lit 8749777650990202050325983592797630370733395301147306988215992320000000000000000000000000000000

noncomputable def p14022 :=
@p14018 p12265 p13949 p12348
  p14019 p12381 p14020 p14021
  p13998 p13980 p13999 p13982

noncomputable def p14023 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 2 1) p13798
  2 1 0 1 p13955 p12189

noncomputable def p14024 :=
@Neg.neg Real Real.instNeg
  (p13792
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p13717 (Enclosure.sfrac false 1 16)))))

noncomputable def p14025 :=
@Enclosure.Real.IsNear.of_eq
  (@iteratedDeriv Real c11 Real
    Real.normedAddCommGroup
    c8
    (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
      (Enclosure.sfrac false 12 1)))
  (p13716
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14024
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p13798
        (Zeta.RiemannSiegel.correction
          (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
            (Enclosure.sfrac false 12 1))))))

noncomputable def p14026 :=
@p13720
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14024
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p13798
      (Zeta.RiemannSiegel.correction
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
          (Enclosure.sfrac false 12 1)))))
  297304375015245

noncomputable def p14027 :=
nat_lit 4755210703481580072836615935106227381766107014746965875

noncomputable def p14028 :=
nat_lit 39613550116288026254041209606841361261098483803204079974346302127230617

noncomputable def p14029 :=
nat_lit 124341818988543224837797873658440016281664885882880000000000000000000000000000000

noncomputable def p14030 :=
@p14026 70368744177664 4717 70368744177664 p14027
  p12261 p14028 p14029 p14019
  p12381 p14020 p14021

noncomputable def p14031 :=
nat_lit 115313387794586922514225695593884612121025

noncomputable def p14032 :=
nat_lit 43556142965880123323311949751266331066368

noncomputable def p14033 :=
@Enclosure.Real.IsNear.subLit_ff_n p14024
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p13798
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
        (Enclosure.sfrac false 12 1))))
  p14031 p14032

noncomputable def p14034 :=
nat_lit 6473994418673340712768329136344433086318225687

noncomputable def p14035 :=
nat_lit 207691874341393105141219853168803840000000000000000000000

noncomputable def p14036 :=
nat_lit 69670876991297975795147618599389333124771074778505250675

noncomputable def p14037 :=
nat_lit 35737672715247666670746057574103723412642103842406024021536318127230617

noncomputable def p14038 :=
nat_lit 207118637233727096743963519475449620829153357402724959488993651034505519878109311648181256192000

noncomputable def p14039 :=
@p14033 p14034 p14035 p14036
  p12261 p14037 p14029 p14038
  p14027 p12261 p14028 p14029

noncomputable def p14040 :=
@Enclosure.Real.IsNear.neg
  (p13792
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p13717 (Enclosure.sfrac false 1 16)))))

noncomputable def p14041 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p14042 :=
@p14041
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p13717 (Enclosure.sfrac false 1 16))))
  p13880

noncomputable def p14043 :=
@p14042 p12265 p13881 p12267
  8742552448095 8796093022208 4068320057 453548546457600000000
  p14031 p14032 p14034 p14035

noncomputable def p14044 :=
p14043
  (p13887 d197
    (p13889 (p13891 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (@p13894 34970209792380 35184372088832 4265942772088832
    p12185 8742552448095 8796093022208 4068320057
    453548546457600000000 (p13922 (Eq.refl true))
    (Eq.refl true))

noncomputable def p14045 :=
@Enclosure.Real.IsNear.mulLit_ff p13798
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
      (Enclosure.sfrac false 12 1)))
  p13955 p12189 p13949

noncomputable def p14046 :=
nat_lit 1152393574327105771130792985

noncomputable def p14047 :=
nat_lit 1445218387159937364743459

noncomputable def p14048 :=
nat_lit 31915641637826210212243046400000000

noncomputable def p14049 :=
@p13720
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p13717 (Enclosure.sfrac false 1 16))))
  297304375015245

noncomputable def p14050 :=
@p14049 70368744177664 4717 70368744177664 3876140653053
  35184372088832 4068320057 453548546457600000000 p14046
  p2333 p14047 p14048

noncomputable def p14051 :=
p14050
  (p13810
    (@Enclosure.Real.IsNear.neg p13724 false 297304375015245 70368744177664
      4717 70368744177664 (p13837 (Eq.refl true))))
  (@p13752 3876140653053 35184372088832 4265942772088832
    p12185 3876140653053 35184372088832 4068320057
    453548546457600000000 (p13945 (Eq.refl true))
    (Eq.refl true))

noncomputable def p14052 :=
@p14045 p13957 p14046 p2333
  p14047 p14048 p14036 p12261
  p14037 p14029
  (@p13958 true p13955 p12189 p13949
    p13957 (p13973 (Eq.refl true)))
  (@p13718 false p14046 p2333 p14047
    p14048
    (BSN.correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
        (Enclosure.sfrac false 12 1))
      (p13719 (Eq.refl true) (Eq.refl true)
        (p13496 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p14051 (Eq.refl true)))

noncomputable def p14053 :=
p14030
  (p13810
    (@Enclosure.Real.IsNear.neg p13724 false 297304375015245 70368744177664
      4717 70368744177664 (p13837 (Eq.refl true))))
  (p14039
    (@p14040 true p14031 p14032 p14034
      p14035 (p14044 (Eq.refl true)))
    (p14052 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p14054 :=
p14022
  (@p14023 p13949 p13957 p13955
    p12265 p13949 p12348
    (Enclosure.Real.IsNear.const false 2 1)
    (@p13958 true p13955 p12189 p13949
      p13957 (p13973 (Eq.refl true)))
    (Eq.refl true))
  (@p14025 false p14019 p12381 p14020
    p14021
    (BSN.deriv_correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
        (Enclosure.sfrac false 12 1))
      (p13719 (Eq.refl true) (Eq.refl true)
        (p13496 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p14053 (Eq.refl true)))

noncomputable def p14055 :=
nat_lit 13023797352141509008890875230969163652795025

noncomputable def p14056 :=
nat_lit 2480353456169254664669633168349659413316654219253396141418771

noncomputable def p14057 :=
@Enclosure.Real.IsNear.mulLit_ff p13800
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
      (Enclosure.sfrac false 12 1)))
  p14055 p12450 p14056

noncomputable def p14058 :=
nat_lit 16732987923012628099756482310963200000000000000000000000000000000000000

noncomputable def p14059 :=
@Enclosure.Real.IsNear.neg
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 4 1)
      c16)
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
          (Enclosure.sfrac false 12 1)))))

noncomputable def p14060 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 4 1)
    c16)
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
        (Enclosure.sfrac false 12 1))))
  p1068

noncomputable def p14061 :=
@p14060 p1070 p1071 p1072
  16655524012681 70368744177664 3405780739 907097092915200000000
  p14055 p12450 p14056 p14058

noncomputable def p14062 :=
p14061 d201
  (@p13728 16655524012681 70368744177664 3571219944177664
    p4996 16655524012681 70368744177664 3405780739
    907097092915200000000
    (p13822 (p13834 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p14063 :=
@p14057 p14058 p14046 p2333
  p14047 p14048 p13987 p13988
  p13989 p13990
  (@p14059 true p14055 p12450 p14056
    p14058 (p14062 (Eq.refl true)))
  (@p13718 false p14046 p2333 p14047
    p14048
    (BSN.correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
        (Enclosure.sfrac false 12 1))
      (p13719 (Eq.refl true) (Eq.refl true)
        (p13496 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p14051 (Eq.refl true)))

noncomputable def p14064 :=
p13983
  (p13810
    (@Enclosure.Real.IsNear.neg p13724 false 297304375015245 70368744177664
      4717 70368744177664 (p13837 (Eq.refl true))))
  (p13992
    (p14017 (p14054 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true))
    (p14063 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p14065 :=
p13954
  (@p13956 p13949 p13957 p13947
    p12189 p13949 p13950
    (Enclosure.Real.IsNear.const false 3 1)
    (@p13958 true p13955 p12189 p13949
      p13957 (p13973 (Eq.refl true)))
    (Eq.refl true))
  (@p13977 false p13951 p12231 p13952
    p13953
    (BSN.iteratedDeriv_two_correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
        (Enclosure.sfrac false 12 1))
      (p13719 (Eq.refl true) (Eq.refl true)
        (p13496 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p14064 (Eq.refl true)))

noncomputable def p14066 :=
@p13863 p13849 p13808
  (@p13872 p13858 p13859
    (p13923 (Eq.refl true)) (p13946 (Eq.refl true))
    (Eq.refl true) (Eq.refl true))
  (p14065 (Eq.refl true)) (Eq.refl true) (Eq.refl true)

noncomputable def p14067 :=
nat_lit 39071392056424527026672625692907490958385075

noncomputable def p14068 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 3 1) p13800)
  (@iteratedDeriv Real c11 Real
    Real.normedAddCommGroup
    c8
    (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
      (Enclosure.sfrac false 12 1)))
  p14067

noncomputable def p14069 :=
nat_lit 5577662641004209366585494103654400000000000000000000000000000000000000

noncomputable def p14070 :=
@p14068 p12450 p14056 p14069
  p14019 p12381 p14020 p14021
  p13850 p13851 p13852 p13853

noncomputable def p14071 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 3 1) p13800
  3 1 0 1 p14055 p12450

noncomputable def p14072 :=
p14070
  (@p14071 p14056 p14058 p14067
    p12450 p14056 p14069
    (Enclosure.Real.IsNear.const false 3 1)
    (@p14059 true p14055 p12450 p14056
      p14058 (p14062 (Eq.refl true)))
    (Eq.refl true))
  (@p14025 false p14019 p12381 p14020
    p14021
    (BSN.deriv_correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
        (Enclosure.sfrac false 12 1))
      (p13719 (Eq.refl true) (Eq.refl true)
        (p13496 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p14053 (Eq.refl true)))

noncomputable def p14073 :=
nat_lit 47274808514527076907283233717927454054042931558839066063875

noncomputable def p14074 :=
nat_lit 196159429230833773869868419475239575503198607639501078528

noncomputable def p14075 :=
nat_lit 66948858863551630508789816490447793927828488966354354719644752509896036183262910479557

noncomputable def p14076 :=
@Enclosure.Real.IsNear.mulLit_tf p13802
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
      (Enclosure.sfrac false 12 1)))
  p14073 p14074 p14075

noncomputable def p14077 :=
nat_lit 71867635893702203483464717089589446259507200000000000000000000000000000000000000000000000000000

noncomputable def p14078 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 8 1)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      c16 Real.pi))
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
        (Enclosure.sfrac false 12 1))))

noncomputable def p14079 :=
@p14078 p1059 p1061 p1062
  p1063 68369245110681 70368744177664 3405780739
  907097092915200000000 p14073 p14074 p14075

noncomputable def p14080 :=
@p14079 p14077 d202
  (@p13961 68369245110681 70368744177664 3571219944177664
    p4996 68369245110681 70368744177664 3405780739
    907097092915200000000
    (p13963 (p13972 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p14081 :=
@p14076 p14077 p14046 p2333
  p14047 p14048 p13841 p13842
  p13843 p13844 (p14080 (Eq.refl true))
  (@p13718 false p14046 p2333 p14047
    p14048
    (BSN.correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
        (Enclosure.sfrac false 12 1))
      (p13719 (Eq.refl true) (Eq.refl true)
        (p13496 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p14051 (Eq.refl true)))

noncomputable def p14082 :=
p13809
  (p13810
    (@Enclosure.Real.IsNear.neg p13724 false 297304375015245 70368744177664
      4717 70368744177664 (p13837 (Eq.refl true))))
  (p13846
    (@p13855 p13840 p13808 p14066
      (p14072 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true))
    (p14081 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p14083 :=
@p13791 p13783
  (@p13803 false p13787 p13788 p13789
    p13790
    (BSN.iteratedDeriv_three_correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
        (Enclosure.sfrac false 12 1))
      (p13719 (Eq.refl true) (Eq.refl true)
        (p13496 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p14082 (Eq.refl true)))

noncomputable def p14084 :=
@p13781 p13782 p13783 1351471939 17179869184
  1 17179869184 p13712 p13688 p13713
  p13690
  (@p13785 p13780 p13782 p13783
    (BSN.correctionLinear_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p13493
        (Enclosure.sfrac false 12 1)))
    (@Enclosure.Real.IsNear.neg p13784 false p13779 p13780
      p13782 p13783
      (p14083 d203 (Eq.refl true))))

noncomputable def p14085 :=
@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv p13493) false
  1351471939 17179869184 1 17179869184 1351471939
  17179869184

noncomputable def p14086 :=
@Enclosure.Real.IsNear.inv_image p13493 218389961743 17179869184 41
  17179869184 675735969 675735970 8589934592
  (p13706 (Eq.refl true)) (Eq.refl true) (Eq.refl true)

noncomputable def p14087 :=
p13778
  (p14084
    (@p14085 1 17179869184
      (p14086 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (Eq.refl true))
    (Eq.refl true))

noncomputable def p14088 :=
@p13691 p13488
  (@p13693 8589934592
    (@p2563 1 0 1
      (BSN.neg_one_pow_even_mk 12 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1))
    p13709 (Eq.refl true))
  (p14087 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p14089 :=
@p13495 p13485 p13487 p13488
  (BSN.hardyZApproximantRS_eq
    (@OfScientific.ofScientific Real c2 101532600
      true 5)
    12
    (p13496 (Eq.refl true) (Eq.refl true)
      (Eq.refl true)))
  (p13685 p14088 (Eq.refl true) (Eq.refl true))

theorem d214 : p13486 p13487 p13488 :=
@p13489 p13485 p13487 p13488
  (@Eq.refl Real
    (hardyZApproximantRS
      (@OfScientific.ofScientific Real c2 101532600
        true 5)))
  p14089

noncomputable def p14090 :=
nat_lit
  2426926902613651420725962896757179096182600329081143099236133459147817994446558419068539137947918555536044003534958317312640441431724299436510290014421645710236817478346698760943949181919

noncomputable def p14091 :=
nat_lit
  1087770609288739018116276647019455748771006705104961378712461595034426490595025393129804804639189577049885346787832834079429794483512744426310696916513970896780966442670885312576979206144

noncomputable def p14092 :=
Enclosure.Real.IsNear
  (hardyZApproximantRS
    (@OfScientific.ofScientific Real c2 101655800
      true 5))
  true p14090 p14091

noncomputable def p14093 :=
nat_lit
  34185700502283649384295196535873630919296649641991357198814348583291194050503504405431813450876458833341912027031830423046301708385961864909810083542619083178405567065081720265544094982645500850824214040127009509395974547505782972669166769

noncomputable def p14094 :=
nat_lit
  10538975498545110118516655086564873663313797681449337828036505974177586242977800625494571949639530566325118728413660708079822755730958726679483787322087498240484389683200000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p14095 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZApproximantRS
    (@OfScientific.ofScientific Real c2 101655800
      true 5))
  (hardyZApproximantRS
    (@OfScientific.ofScientific Real c2 101655800
      true 5))
  true p14090

noncomputable def p14096 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
  (Zeta.RiemannSiegel.mainSumOfPhase
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101655800
        true 5))
    (@OfScientific.ofScientific Real c2 101655800
      true 5)
    12)

noncomputable def p14097 :=
@HPow.hPow Real Real Real (@instHPow Real Real Real.instPow)
  (@HDiv.hDiv Real Real Real c4
    (@OfScientific.ofScientific Real c2 101655800
      true 5)
    c7)

noncomputable def p14098 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  c22
  (p14097
    (@Neg.neg Real Real.instNeg
      (@HDiv.hDiv Real Real Real c4
        c38
        c20)))

noncomputable def p14099 :=
Real.sqrt
  (@HDiv.hDiv Real Real Real c4
    (@OfScientific.ofScientific Real c2 101655800
      true 5)
    c7)

noncomputable def p14100 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p14098
  (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
        (Enclosure.sfrac false 12 1)))
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Zeta.RiemannSiegel.correctionLinear
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
          (Enclosure.sfrac false 12 1)))
      (@Inv.inv Real Real.instInv p14099)))

noncomputable def p14101 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZApproximantRS
    (@OfScientific.ofScientific Real c2 101655800
      true 5))
  (p14096 p14100) true p14090

noncomputable def p14102 :=
@BSN.floor_sqrt_eq_dec
  (@OfScientific.ofScientific Real c2 101655800
    true 5)
  101655800 100000 12
  (Enclosure.sfrac_ofScientific_eq 101655800 5 100000 (Eq.refl true))

noncomputable def p14103 :=
@Enclosure.Real.IsNear.subLit_tf
  (Zeta.RiemannSiegel.mainSumOfPhase
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101655800
        true 5))
    (@OfScientific.ofScientific Real c2 101655800
      true 5)
    12)

noncomputable def p14104 :=
nat_lit
  143691092660175609506364595051021629621349270230466537061828103290025997844966877334867733935997410437924951157731471558421377754351634184807853883233376915634327481637355485482420138975

noncomputable def p14105 :=
nat_lit
  693372686070125132169890678980630832438270944067208030691549706822162858182043926727229439797062220457264934277894685984925546573493615743070301138162992323391167065081720265544094982645500850824214040127009509395974547505782972669166769

noncomputable def p14106 :=
nat_lit
  166777146824131356402591155514904138741105709722277557464244412616499685054532448474445414079717483956781899910392869849295700853700148527493166783670661386879453175753924149245087741206848952336384

noncomputable def p14107 :=
@p14103 p14100 144242516561 68719476736 218387
  68719476736 p14104 p14091 p14105
  p14094 p14106 p14090

noncomputable def p14108 :=
@Enclosure.Real.IsNear.of_eq
  (Zeta.RiemannSiegel.mainSumOfPhase
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101655800
        true 5))
    (@OfScientific.ofScientific Real c2 101655800
      true 5)
    12)

noncomputable def p14109 :=
@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101655800
        true 5))
    (@OfScientific.ofScientific Real c2 101655800
      true 5)
    12)

noncomputable def p14110 :=
p14109
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101655800
        true 5))
    (@OfScientific.ofScientific Real c2 101655800
      true 5)
    12)

noncomputable def p14111 :=
@p14108 p14110 true 144242516561 68719476736
  218387 68719476736
  (BSN.main_sum_of_phase_eq
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101655800
        true 5))
    (@OfScientific.ofScientific Real c2 101655800
      true 5)
    12)

noncomputable def p14112 :=
@Enclosure.Real.IsNear.addLit_tt
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101655800
        true 5))
    (@OfScientific.ofScientific Real c2 101655800
      true 5)
    12)

noncomputable def p14113 :=
@p14112
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101655800
        true 5))
    (@OfScientific.ofScientific Real c2 101655800
      true 5)
    12)

noncomputable def p14114 :=
@p14113 144242516561 137438953472 218387 137438953472
  144242516561 137438953472 218387 137438953472
  39649081044622936899584 144242516561 68719476736

noncomputable def p14115 :=
BSN.mainSumRS_step
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real c2 101655800
      true 5))
  (@OfScientific.ofScientific Real c2 101655800
    true 5)
  Real.cos BSN.quadSignNeg

noncomputable def p14116 :=
p14115 11 12 101655800 100000 286
  137438953472 68719476736 2305843009213693952 false 285404097463511
  3368

noncomputable def p14117 :=
p14116 341522969406 43 39675208392 8 true
  105488140238 204786 true 29668734020 7244019458077122842 1

noncomputable def p14118 :=
p14117 false 134249097613 true true 144242516561 218387
  BSN.abs_quadSignNeg (BSN.cos_quad_nat2 286 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 134249097613 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101655800 5 100000 (Eq.refl true))
  (Eq.refl true)

noncomputable def p14119 :=
BSN.mainSumRS_step2
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real c2 101655800
      true 5))
  (@OfScientific.ofScientific Real c2 101655800
    true 5)
  Real.cos Real.sin

noncomputable def p14120 :=
p14119 BSN.quadSignPos BSN.quadSignNeg 9 10 11 101655800
  100000 168 229 137438953472 68719476736

noncomputable def p14121 :=
p14120 2305843009213693952 false 285404097463511 3368
  316464885454 43 43462013224 8 329564216814 43
  41439403656

noncomputable def p14122 :=
p14121 8 true 107891785059 175683 true 31528214081
  true 178553503126 7244019458077122842 1 false

noncomputable def p14123 :=
p14122 133838530156 false false 132399046672 true true
  105488140238 204786 BSN.abs_quadSignPos
  (BSN.cos_quad_nat0 168 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 133838530156 137438953472)

noncomputable def p14124 :=
BSN.mainSumRS_step2
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real c2 101655800
      true 5))
  (@OfScientific.ofScientific Real c2 101655800
    true 5)
  Real.sin Real.sin

noncomputable def p14125 :=
p14124 BSN.quadSignPos BSN.quadSignPos 7 8 9 101655800
  100000 23 99 137438953472 68719476736

noncomputable def p14126 :=
p14125 2305843009213693952 false 285404097463511 3368
  285796269294 43 48592008000 16 301984246446 43
  45812984488

noncomputable def p14127 :=
p14126 8 true 198099259364 143317 true 158948582194
  true 207432411178 7244019458077122842 1 false

noncomputable def p14128 :=
p14127 125811765702 false false 137178893903 false true
  107891785059 175683 BSN.abs_quadSignPos
  (BSN.cos_quad_nat3 23 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 125811765702 137438953472)

noncomputable def p14129 :=
BSN.mainSumRS_step2
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real c2 101655800
      true 5))
  (@OfScientific.ofScientific Real c2 101655800
    true 5)
  Real.cos Real.cos

noncomputable def p14130 :=
p14129 BSN.quadSignNeg BSN.quadSignNeg 5 6 7 101655800
  100000 162 62 137438953472 68719476736

noncomputable def p14131 :=
p14130 2305843009213693952 false 285404097463511 3368
  246257546308 43 56109217800 8 267443854420 43
  51947041624

noncomputable def p14132 :=
p14131 8 true 129863274247 106282 false 95064973622
  false 146814299138 7244019458077122842 1 false

noncomputable def p14133 :=
p14132 105851356538 true false 66202914693 true true
  198099259364 143317 BSN.abs_quadSignNeg
  (BSN.cos_quad_nat2 162 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 105851356538 137438953472)

noncomputable def p14134 :=
p14129 BSN.quadSignPos BSN.quadSignPos 3 4 5 101655800
  100000 424 280 137438953472 68719476736

noncomputable def p14135 :=
p14134 2305843009213693952 false 285404097463511 3368
  190530846192 42 68719476728 8 221199462352 42
  61464568544

noncomputable def p14136 :=
p14135 16 true 194658786155 62622 false 181673732786
  false 93205497627 7244019458077122842 1 false

noncomputable def p14137 :=
p14136 33862558091 false false 107027678377 false true
  129863274247 106282 BSN.abs_quadSignPos
  (BSN.cos_quad_nat0 424 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 33862558091 137438953472)

noncomputable def p14138 :=
p14124 BSN.quadSignNeg BSN.quadSignPos 1 2 3 101655800
  100000 873 611 137438953472 68719476736

noncomputable def p14139 :=
p14138 2305843009213693952 false 285404097463511 3368
  95265423088 42 97184016000 16 150992123216 42
  79350416784

noncomputable def p14140 :=
p14139 16 true 137437481632 3418 false 90518843256
  false 3910071893 7244019458077122842 1 false

noncomputable def p14141 :=
p14140 84115274597 true false 3909544461 false true
  194658786155 62622 BSN.abs_quadSignNeg
  (BSN.cos_quad_nat1 873 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 84115274597 137438953472)

noncomputable def p14142 :=
@Enclosure.Real.IsNear.recentre'
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101655800
        true 5))
    (@OfScientific.ofScientific Real c2 101655800
      true 5)
    1)

noncomputable def p14143 :=
@Enclosure.Real.IsNear.of_eq
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101655800
        true 5))
    (@OfScientific.ofScientific Real c2 101655800
      true 5)
    1)

noncomputable def p14144 :=
@p14143
  (Real.cos
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101655800
        true 5)))
  true 4294921301

noncomputable def p14145 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101655800
        true 5)))
  true 17179685204

noncomputable def p14146 :=
@Enclosure.Real.IsNear.cos_image
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real c2 101655800
      true 5))
  (@HDiv.hDiv Real Real Real c4
    (@Nat.cast Real Real.instNatCast 17837756091469)
    (@Nat.cast Real Real.instNatCast 8589934592))
  false 17837756091469

noncomputable def p14147 :=
nat_lit 2902658608423150406796283599589146769891011544433402664373

noncomputable def p14148 :=
nat_lit 1397801800933056941352431117493786966555774720933888000

noncomputable def p14149 :=
@Enclosure.Real.IsNear.recentre'
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real c2 101655800
      true 5))
  false p14147 p14148

noncomputable def p14150 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 101655800 400000)
      (Real.log (Enclosure.sfrac false 41335616694560000 160000000000)))
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 1 4)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 1 2) Real.pi)
        (Real.arctan
          (@HDiv.hDiv Real Real Real c4
            (@Nat.cast Real Real.instNatCast 100000)
            (@Nat.cast Real Real.instNatCast 203311600))))))

noncomputable def p14151 :=
nat_lit 521077494082926890002786340848640000000000000000

noncomputable def p14152 :=
nat_lit 3178233330193181567102399452537126686720000000000000

noncomputable def p14153 :=
@Enclosure.Real.IsNear.of_eq
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real c2 101655800
      true 5))
  (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (p14150 (Enclosure.sfrac false 101655800 200000))
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 101655800 200000) (Real.log Real.pi)))
    (Enclosure.sfrac true p14151 p14152))
  false

noncomputable def p14154 :=
BSN.riemannSiegelThetaApproximant_two_zero_mk
  (@OfScientific.ofScientific Real c2 101655800
    true 5)
  101655800 100000 41335616694560000 160000000000

noncomputable def p14155 :=
p14154 203311600 400000 200000 p14151
  p14152
  (Enclosure.sfrac_ofScientific_eq 101655800 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p14156 :=
@Enclosure.Real.IsNear.addLit_ft_p
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (p14150 (Enclosure.sfrac false 101655800 200000))
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 101655800 200000) (Real.log Real.pi)))
  (Enclosure.sfrac true p14151 p14152) 18704244408116386297857
  9007199254740992000

noncomputable def p14157 :=
nat_lit 59446448300506120331187888119585725847367916429996086566359040000000000000

noncomputable def p14158 :=
@p14156 847754322644250347 p3054 p14151
  p14152 0 1 p14157 p14147
  p14148 847754322644250347 p3054

noncomputable def p14159 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (p14150 (Enclosure.sfrac false 101655800 200000))
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 101655800 200000) (Real.log Real.pi))
  23945012692861886363649 9007199254740992000 640633902769 66000000000000000000

noncomputable def p14160 :=
nat_lit 1285345888468012097775973278154752000

noncomputable def p14161 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 101655800 400000)
      (Real.log (Enclosure.sfrac false 41335616694560000 160000000000)))
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 1 4)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 1 2) Real.pi)
        (Real.arctan
          (@HDiv.hDiv Real Real Real c4
            (@Nat.cast Real Real.instNatCast 100000)
            (@Nat.cast Real Real.instNatCast 203311600))))))

noncomputable def p14162 :=
@p14161 (Enclosure.sfrac false 101655800 200000)
  28523182922862383036417 9007199254740992000 640633902769 66000000000000000000
  101655800 200000 0

noncomputable def p14163 :=
nat_lit 4789002538572377272729800000

noncomputable def p14164 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 101655800 400000)
    (Real.log (Enclosure.sfrac false 41335616694560000 160000000000)))
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 1 4)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 1 2) Real.pi)
      (Real.arctan
        (@HDiv.hDiv Real Real Real c4
          (@Nat.cast Real Real.instNatCast 100000)
          (@Nat.cast Real Real.instNatCast 203311600)))))
  28526718934177637960417

noncomputable def p14165 :=
nat_lit 64228497991411761597663775040959676416

noncomputable def p14166 :=
@p14164 9007199254740992000 635633894519 66000000000000000000
  884002828813731 2251799813685248 20000033 264000000000000000
  p14165 28523182922862383036417 9007199254740992000 640633902769

noncomputable def p14167 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 101655800 400000)
  (Real.log (Enclosure.sfrac false 41335616694560000 160000000000)) 101655800
  400000 0 1 56124134450130023 4503599627370496

noncomputable def p14168 :=
nat_lit 30854569213390770141789159424

noncomputable def p14169 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv Real Real Real c4
      (@Nat.cast Real Real.instNatCast 41335616694560000)
      (@Nat.cast Real Real.instNatCast 160000000000)))
  false p14168 p2333

noncomputable def p14170 :=
BSN.log_rat_reduce_isNear 41335616694560000 160000000000 17 82671233389120000
  41943040000000000 46630232555 68719476736 24973259072661432
  36028797018963968 26400000000 1000000000000000

noncomputable def p14171 :=
nat_lit
  954641307989432573045240757327453741944230685128499231532139777040874455572128858621092395631100342631513072712106608113207015348000552913186073650260496038013483339429864624575963999858380917415639678598610778510429616771596235999895327428945253361210751552243969504341079341129821570727936000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p14172 :=
nat_lit
  36351739917326694695042332035253169904391727304142695867605602593563009220058543978580981269962593570055587477139292509911040538457399120091248767832356500197933477802688220170296989009936720463436911449909207066385250158820795710146657757353099440224588477743612117962767194231278289918361600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p14173 :=
nat_lit
  857658179093343374099157461230012262993449507768122569270392025173051706039031513398673248885206817852668628132151105369366158299260208940374373484191563382205685777559783842061232271163861031641501443963511744205546197560552712112272715688409620207459390843075946000429384466432000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p14174 :=
BSN.log_dyadic_bound 20364096694560000 62307136694560000 12 11
  p14171 68719476736 26400000000 p14172 p14173
  46630232555 82671233389120000

noncomputable def p14175 :=
p14174 41943040000000000 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p14176 :=
@BSN.binarySplit_of_base11 (BSN.artanhP 20364096694560000) (BSN.artanhQ 62307136694560000)
  0 11 p14172 p14171 p14173
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p14177 :=
p14170 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p14175 (p14176 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

noncomputable def p14178 :=
@p14167 1250561 33000000000000000 28526718934177637960417
  9007199254740992000 635633894519 66000000000000000000
  (Enclosure.Real.IsNear.const false 101655800 400000)
  (BSN.isNear_log_sfrac 41335616694560000 160000000000 56124134450130023
    4503599627370496 1250561 33000000000000000 false
    (@p14169 1000448800000000 p2422 56124134450130023
      4503599627370496 1250561 33000000000000000
      (p14177 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p14179 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 1 4)
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 1 2) Real.pi)
    (Real.arctan
      (@HDiv.hDiv Real Real Real c4
        (@Nat.cast Real Real.instNatCast 100000)
        (@Nat.cast Real Real.instNatCast 203311600))))
  1 4

noncomputable def p14180 :=
@p14179 0 1 884002828813731 562949953421312 20000033
  66000000000000000 884002828813731 2251799813685248 20000033
  264000000000000000 (Enclosure.Real.IsNear.const false 1 4)

noncomputable def p14181 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 1 2) Real.pi)
  (Real.arctan
    (@HDiv.hDiv Real Real Real c4
      (@Nat.cast Real Real.instNatCast 100000) (@Nat.cast Real Real.instNatCast 203311600)))
  884279719003555 562949953421312 1

noncomputable def p14182 :=
nat_lit 7593526478652922241482752

noncomputable def p14183 :=
@p14181 2000000000000000 4225009 8589934592 1
  3300000000 p14182 884002828813731 562949953421312 20000033
  66000000000000000
  (@p803 1 1000000000000000 884279719003555 562949953421312
    1 2000000000000000 (Enclosure.Real.IsNear.const false 1 2)
    BSN.pi_near_15 (Eq.refl true))

noncomputable def p14184 :=
BSN.arctan_dyadic_bound_f 100000 203311600 1 0 8589934592
  3300000000 0 1 1 0 1

noncomputable def p14185 :=
p14184 1 4225009 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)
  (@BSN.binarySplit_of_le (BSN.arctanEvenP 100000) (BSN.arctanEvenQ 203311600) 0
    0 (Eq.refl true))
  (@BSN.binarySplit_of_le (BSN.arctanOddP 100000) (BSN.arctanOddQ 203311600) 0 0
    (Eq.refl true))

noncomputable def p14186 :=
p14180
  (p14183
    (p14185 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p14187 :=
@p14159 39983888891185761 68719476736000 508279 34359738368000
  p14160 18704244408116386297857 9007199254740992000 847754322644250347
  p3054
  (@p14162 1 p14163 23945012692861886363649
    9007199254740992000 640633902769 66000000000000000000
    (@p14166 66000000000000000000 p14178 p14186
      (Eq.refl true) (Eq.refl true))
    (Enclosure.Real.IsNear.const false 101655800 200000) (Eq.refl true)
    (Eq.refl true))

noncomputable def p14188 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 101655800 200000) (Real.log Real.pi)
  101655800 200000 0 1 78665238759 68719476736

noncomputable def p14189 :=
p14187
  (@p14188 1 34359738368 39983888891185761 68719476736000
    508279 34359738368000
    (Enclosure.Real.IsNear.const false 101655800 200000) d91
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p14190 :=
@p14146 8589934592 211 8589934592 true 17179685204
  17179869184 1 3300000000
  (@p14149 847754322644250347 p3054 17837756091469
    8589934592 211 8589934592
    (@p14153 p14147 p14148 847754322644250347
      p3054
      (p14155 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p14158 (p14189 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p14151 p14152)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p14191 :=
nat_lit 1938822524413902354967953408

noncomputable def p14192 :=
BSN.cos_reduce1
  (@HDiv.hDiv Real Real Real c4
    (@Nat.cast Real Real.instNatCast 17837756091469)
    (@Nat.cast Real Real.instNatCast 8589934592))
  (@HDiv.hDiv Real Real Real c4
    (@Nat.cast Real Real.instNatCast p14191)
    (@Nat.cast Real Real.instNatCast p2445))
  226375608064910080 72057594037927936 false

noncomputable def p14193 :=
BSN.sin_reduce_arg_pos_rat_q1 17837756091469 8589934592 226375608064910080
  72057594037927936 330 p14191 p2445
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p14194 :=
nat_lit
  1125936879753373431752202045433383941963055733404174398549516757456071015183080226202499180623561159434177599741454526382433461083615202069076046640276873757960580897181696

noncomputable def p14195 :=
nat_lit
  783897031404130442222300290219023816493953107920696306010435494645354459018161380413712739281415472315668625003458423447156147584303383127822893390075555194450743296

noncomputable def p14196 :=
nat_lit
  5622770774686336244785774671758258229953503125128445739692750024828267458869367411700201122976544039264905440474449426774927943200958401459605705704112535632671823223853056

noncomputable def p14197 :=
BSN.sin_dyadic_bound_f 55104650426014 35184372088832 4 3 17179869184
  6606445313 p14194 p3100 p14195
  p14196 p3103

noncomputable def p14198 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 55104650426014) (BSN.sinEvenQ 35184372088832) 0
  3 p14194 p3100 p14195 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p14199 :=
p14197 p14195 17179685204 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p14198 (Eq.refl true))

noncomputable def p14200 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 55104650426014) (BSN.sinOddQ 35184372088832) 0
  3 p14196 p3103 p14195 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p14201 :=
@BSN.sin_arg_round false 17179685204 17179869184 p14191
  p2445 55104650426014 35184372088832 6606445313 6600000000
  (p14199 (p14200 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p14202 :=
p14192 17179685204 17179869184 330 1000000000000000
  6600000000 3300000000 p14193 BSN.pi_near_15 p14201
  (Eq.refl true) (Eq.refl true)

noncomputable def p14203 :=
@p14144 4294967296 2753476307 110729625600000000
  (BSN.main_sum_rs_one
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101655800
        true 5))
    (@OfScientific.ofScientific Real c2 101655800
      true 5))
  (@p14145 17179869184 704889934592 28346784153600000000
    4294921301 4294967296 2753476307 110729625600000000
    (p14190 (Enclosure.sfrac_false_div 17837756091469 8589934592)
      (p14202 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p14204 :=
@p14142 true 4294921301 4294967296 2753476307
  110729625600000000 137437481632 137438953472 3418 137438953472
  p14203 (Eq.refl true)

noncomputable def p14205 :=
p14141 BSN.abs_quadSignPos (BSN.cos_quad_nat3 611 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 3909544461 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101655800 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true) p14204
  (@p14149 847754322644250347 p3054 285404097463511
    137438953472 3368 137438953472
    (@p14153 p14147 p14148 847754322644250347
      p3054
      (p14155 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p14158 (p14189 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p14151 p14152)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p14206 :=
nat_lit 72444287956147241365650522890286684090105328107605819156288401644637800231068074378096803840

noncomputable def p14207 :=
nat_lit 4507253281720282673913374120429220205965247393323192663341974120280666659740323325935616

noncomputable def p14208 :=
nat_lit 189727742427453323119041224011698715784228106071759384049776593492142355716300615228678209536

noncomputable def p14209 :=
BSN.sin_dyadic_bound_f 90518843256 137438953472 3 2 137438953472
  68719476736 p14206 p2477 p14207
  p14208 p2480

noncomputable def p14210 :=
@BSN.binarySplit_of_base2 (BSN.sinEvenP 90518843256) (BSN.sinEvenQ 137438953472) 0
  2 p14206 p2477 p14207 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p14211 :=
p14209 p14207 84115274597 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p14210 (Eq.refl true))

noncomputable def p14212 :=
@BSN.binarySplit_of_base2 (BSN.sinOddP 90518843256) (BSN.sinOddQ 137438953472) 0
  2 p14208 p2480 p14207 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p14213 :=
nat_lit 233743192123432981970073211700494695601

noncomputable def p14214 :=
BSN.sin_dyadic_bound_f 3910071893 137438953472 2 1 137438953472
  68719476736 p14213 p3178 p14213
  p14213 p3179

noncomputable def p14215 :=
@BSN.binarySplit_of_base (BSN.sinEvenP 3910071893) (BSN.sinEvenQ 137438953472) 0
  1 p14213 p3178 p14213 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p14216 :=
p14214 p14213 3909544461 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p14215 (Eq.refl true))

noncomputable def p14217 :=
@BSN.binarySplit_of_base (BSN.sinOddP 3910071893) (BSN.sinOddQ 137438953472) 0 1
  p14213 p3179 p14213 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p14218 :=
p14205 d93 d95 d97 d99 d103
  (p14211 (p14212 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p14216 (p14217 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p14219 :=
p14137 BSN.abs_quadSignPos (BSN.cos_quad_nat0 280 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 107027678377 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101655800 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p14218 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p14149 847754322644250347 p3054 285404097463511
    137438953472 3368 137438953472
    (@p14153 p14147 p14148 847754322644250347
      p3054
      (p14155 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p14158 (p14189 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p14151 p14152)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p14220 :=
nat_lit
  43219894513307830369912319549805559238695202991868722202420331422965895956342198026231838229069529085745155522165116775755887233710275278559626531795819380213311735500252692045793813048918016

noncomputable def p14221 :=
nat_lit
  1408232079226561663646318351109606106503488009201771595884798687254621258396366013368917511507143949531400209595516173250294909858925223686720947124411233085419269397537982146215936

noncomputable def p14222 :=
nat_lit
  440309633813049286073323648225752418529797610996825295724280963569877662606697856155492200308836633298981304242097374651796267446564521294918808645241636606424543748812680768721864813130612736

noncomputable def p14223 :=
BSN.cos_dyadic_bound_f 181673732786 137438953472 5 4 137438953472
  68719476736 p14220 p2495 p14221
  p14222 p2498

noncomputable def p14224 :=
@BSN.binarySplit_of_base4 (BSN.cosEvenP 181673732786) (BSN.cosEvenQ 137438953472) 0
  4 p14220 p2495 p14221 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p14225 :=
p14223 p14221 33862558091 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p14224 (Eq.refl true))

noncomputable def p14226 :=
@BSN.binarySplit_of_base4 (BSN.cosOddP 181673732786) (BSN.cosOddQ 137438953472) 0
  4 p14222 p2498 p14221 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p14227 :=
nat_lit
  191789678484842850490243727277409463341291328258518836106199407332009537932411444059412327387077545617380069102320777803190152130509602734801

noncomputable def p14228 :=
nat_lit
  429831613515143380114695143127427827433318849837230267881748356344765866419332169389098471063862843253523142655748987481619019776721

noncomputable def p14229 :=
nat_lit
  1163426402994017803728658370135156075400868333296217034930302184904190710515244863078888319140658672829848497136809059958760701101535900648145

noncomputable def p14230 :=
BSN.cos_dyadic_bound_f 93205497627 137438953472 4 3 137438953472
  68719476736 p14227 p2457 p14228
  p14229 p2460

noncomputable def p14231 :=
@BSN.binarySplit_of_base3 (BSN.cosEvenP 93205497627) (BSN.cosEvenQ 137438953472) 0
  3 p14227 p2457 p14228 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p14232 :=
p14230 p14228 107027678377 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p14231 (Eq.refl true))

noncomputable def p14233 :=
@BSN.binarySplit_of_base3 (BSN.cosOddP 93205497627) (BSN.cosOddQ 137438953472) 0
  3 p14229 p2460 p14228 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p14234 :=
p14219 d105 d107 d109 d111 d103
  (p14225 (p14226 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p14232 (p14233 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p14235 :=
p14133 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 62 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 66202914693 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101655800 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p14234 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p14149 847754322644250347 p3054 285404097463511
    137438953472 3368 137438953472
    (@p14153 p14147 p14148 847754322644250347
      p3054
      (p14155 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p14158 (p14189 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p14151 p14152)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p14236 :=
nat_lit
  207560991374058838293311995070131446957509778224793489663492519009977949212093546877916092011148749295748904679661234603948579414184121143296

noncomputable def p14237 :=
nat_lit
  544811648247168801684745255391721980121793190093098301609326691767102789700875557266158879801990115519563645682276346062018290978816

noncomputable def p14238 :=
nat_lit
  1259088983649512357001833497266173493837276849686444401849613743381274990427635558925195792921347433995876958136510924428463173995461918658560

noncomputable def p14239 :=
BSN.cos_dyadic_bound_f 95064973622 137438953472 4 3 137438953472
  68719476736 p14236 p2457 p14237
  p14238 p2460

noncomputable def p14240 :=
@BSN.binarySplit_of_base3 (BSN.cosEvenP 95064973622) (BSN.cosEvenQ 137438953472) 0
  3 p14236 p2457 p14237 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p14241 :=
p14239 p14237 105851356538 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p14240 (Eq.refl true))

noncomputable def p14242 :=
@BSN.binarySplit_of_base3 (BSN.cosOddP 95064973622) (BSN.cosOddQ 137438953472) 0
  3 p14238 p2460 p14237 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p14243 :=
nat_lit
  1181447333397135654943431138704324374953639077292729119313442580763680573613417636341509732774729104890818203777355591650054859009021748187136

noncomputable def p14244 :=
nat_lit
  100281373741208630244302454898430463367121499591831785744670899383590097869879618031991136261996446207827460327805534994168424442105856

noncomputable def p14245 :=
nat_lit
  7163746138355186905696140793154915809290939283048150148249801900254438189708301667506596703870632107546979961139846557423987618068165080125440

noncomputable def p14246 :=
BSN.cos_dyadic_bound_f 146814299138 137438953472 4 3 137438953472
  68719476736 p14243 p2457 p14244
  p14245 p2460

noncomputable def p14247 :=
@BSN.binarySplit_of_base3 (BSN.cosEvenP 146814299138) (BSN.cosEvenQ 137438953472) 0
  3 p14243 p2457 p14244 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p14248 :=
p14246 p14244 66202914693 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p14247 (Eq.refl true))

noncomputable def p14249 :=
@BSN.binarySplit_of_base3 (BSN.cosOddP 146814299138) (BSN.cosOddQ 137438953472) 0
  3 p14245 p2460 p14244 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p14250 :=
p14235 d113 d115 d117 d119 d103
  (p14241 (p14242 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p14248 (p14249 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p14251 :=
p14128 BSN.abs_quadSignPos (BSN.cos_quad_nat3 99 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 137178893903 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101655800 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p14250 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p14149 847754322644250347 p3054 285404097463511
    137438953472 3368 137438953472
    (@p14153 p14147 p14148 847754322644250347
      p3054
      (p14155 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p14158 (p14189 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p14151 p14152)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p14252 :=
nat_lit
  4219502868852613190092812631019607051037962091942892400408686481898192833601439871399155755115697280685535425451324443153961928187955123982336

noncomputable def p14253 :=
nat_lit
  260063798057870114723862007616838896414879045111677085741116820472395079111908530970230019823002861653452531797070660293304482902183936

noncomputable def p14254 :=
nat_lit
  21089802562559388969690778913758720011622320721925724885438346994134460284487269285825722568735477726492109703479333184027637458654357110788096

noncomputable def p14255 :=
BSN.sin_dyadic_bound_f 158948582194 137438953472 4 3 137438953472
  68719476736 p14252 p2504 p14253
  p14254 p2507

noncomputable def p14256 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 158948582194) (BSN.sinEvenQ 137438953472) 0
  3 p14252 p2504 p14253 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p14257 :=
p14255 p14253 125811765702 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p14256 (Eq.refl true))

noncomputable def p14258 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 158948582194) (BSN.sinOddQ 137438953472) 0
  3 p14254 p2507 p14253 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p14259 :=
nat_lit
  12252621845813120856140002059324893776615410168094889716378253173170350780333503182617357043690145023657033834628320452336123399110457645142016

noncomputable def p14260 :=
nat_lit
  6346282302767220127484836273540238029000385604024136246197453264201185453042359494471613652877343417324177048534467744905493998295126016

noncomputable def p14261 :=
nat_lit
  61198212066365440386187646549393437812798535947972911711031920492438024141130739605978068140941352798544511386680592595685250374988508371685376

noncomputable def p14262 :=
BSN.sin_dyadic_bound_f 207432411178 137438953472 4 3 137438953472
  68719476736 p14259 p2504 p14260
  p14261 p2507

noncomputable def p14263 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 207432411178) (BSN.sinEvenQ 137438953472) 0
  3 p14259 p2504 p14260 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p14264 :=
p14262 p14260 137178893903 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p14263 (Eq.refl true))

noncomputable def p14265 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 207432411178) (BSN.sinOddQ 137438953472) 0
  3 p14261 p2507 p14260 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p14266 :=
p14251 d121 d123 d125 d127 d103
  (p14257 (p14258 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p14264 (p14265 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p14267 :=
p14123 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 229 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 132399046672 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101655800 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p14266 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p14149 847754322644250347 p3054 285404097463511
    137438953472 3368 137438953472
    (@p14153 p14147 p14148 847754322644250347
      p3054
      (p14155 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p14158 (p14189 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p14151 p14152)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p14268 :=
nat_lit 592306964221992771230387099038119720473177858676935580263827524063646544028770078414123521

noncomputable def p14269 :=
nat_lit 976326250395737525913531597345316550835771007578730815626089187182213322310874083841

noncomputable def p14270 :=
nat_lit 1776918940013477522216109470051164470786431904488791583329851320012565267659665613494202881

noncomputable def p14271 :=
BSN.cos_dyadic_bound_f 31528214081 137438953472 3 2 137438953472
  68719476736 p14268 p2466 p14269
  p14270 p2469

noncomputable def p14272 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP 31528214081) (BSN.cosEvenQ 137438953472) 0
  2 p14268 p2466 p14269 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p14273 :=
p14271 p14269 133838530156 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p14272 (Eq.refl true))

noncomputable def p14274 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP 31528214081) (BSN.cosOddQ 137438953472) 0
  2 p14270 p2469 p14269 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p14275 :=
nat_lit
  6721408175553125201907548877950294132854147284086229329587271230965934134363107178547976041324960735609862480563069470598041274603652861464576

noncomputable def p14276 :=
nat_lit
  1050075444671668066811865734869200796866023208726334491263826952989517179993761280845281853925353538270599995234475572672125149780709376

noncomputable def p14277 :=
nat_lit
  33587484736573379239036791223943133699677593122998505094783073488300619071024428568269468366809586584613423071653805838169821412448949388251136

noncomputable def p14278 :=
BSN.sin_dyadic_bound_f 178553503126 137438953472 4 3 137438953472
  68719476736 p14275 p2504 p14276
  p14277 p2507

noncomputable def p14279 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 178553503126) (BSN.sinEvenQ 137438953472) 0
  3 p14275 p2504 p14276 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p14280 :=
p14278 p14276 132399046672 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p14279 (Eq.refl true))

noncomputable def p14281 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 178553503126) (BSN.sinOddQ 137438953472) 0
  3 p14277 p2507 p14276 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p14282 :=
p14267 d129 d131 d133 d135 d103
  (p14273 (p14274 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p14280 (p14281 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p14283 :=
p14118
  (p14282 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p14149 847754322644250347 p3054 285404097463511
    137438953472 3368 137438953472
    (@p14153 p14147 p14148 847754322644250347
      p3054
      (p14155 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p14158 (p14189 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p14151 p14152)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p14284 :=
nat_lit 464456731834765429203317223526472346034604237842337564024175277012676268964162285772800000

noncomputable def p14285 :=
nat_lit 600332867579077137706978724873733610530661255115262317579505578920663388185600000000

noncomputable def p14286 :=
nat_lit 1393368994838561129455676256621967290636591652204502461547890672026870965565710486118400000

noncomputable def p14287 :=
BSN.cos_dyadic_bound_f 29668734020 137438953472 3 2 137438953472
  68719476736 p14284 p2466 p14285
  p14286 p2469

noncomputable def p14288 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP 29668734020) (BSN.cosEvenQ 137438953472) 0
  2 p14284 p2466 p14285 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p14289 :=
p14287 p14285 134249097613 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p14288 (Eq.refl true))

noncomputable def p14290 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP 29668734020) (BSN.cosOddQ 137438953472) 0
  2 p14286 p2469 p14285 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p14291 :=
p14283 d137 d139 d103
  (p14289 (p14290 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true) (Eq.refl true)

noncomputable def p14292 :=
@p14107 p14091 p14093 p14094
  (p14111
    (@p14114 218387 68719476736
      (p14291 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (p14291 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true) (Eq.refl true)))

noncomputable def p14293 :=
@Enclosure.Real.IsNear.mulLit_ff p14098
  (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
        (Enclosure.sfrac false 12 1)))
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Zeta.RiemannSiegel.correctionLinear
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
          (Enclosure.sfrac false 12 1)))
      (@Inv.inv Real Real.instInv p14099)))

noncomputable def p14294 :=
nat_lit
  59659287713743341416712131343243904581110802952651230992127013657704891540472982259260005854237396541595347579888980701094341334409611880924086933402041779744682187776159616815

noncomputable def p14295 :=
nat_lit
  126633165554229521438977290762059361297987250739820462036000284719563379254544315991201997343356439034674007770120263341747898897565056619503383631412169301973302667340133957632

noncomputable def p14296 :=
nat_lit
  862926904303600565049564611719917814253197664196834802953906067970903518896413128801544973634819907616268684090932626617904314462792149674786690912208904736845053842248811234392517622728956430351970023625968615047433430927533377

noncomputable def p14297 :=
nat_lit
  3680694673167929327528686874976221121607976155861748089560949933078694009330752524137929529989905620340182933169531417572808948717182057448482532283088948428800000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p14298 :=
@p14293 2408528465 8589934592 1 8589934592
  p14294 p14295 p14296 p14297
  p14104 p14091 p14105

noncomputable def p14299 :=
@Enclosure.Real.IsNear.mulLit_ff
  c22
  (p14097
    (@Neg.neg Real Real.instNeg
      (@HDiv.hDiv Real Real Real c4
        c38
        c20)))

noncomputable def p14300 :=
@p14299 1 1 0 1 2408528465 8589934592
  1 8589934592 2408528465 8589934592 1

noncomputable def p14301 :=
@Enclosure.Real.IsNear.of_eq
  (p14097
    (@Neg.neg Real Real.instNeg
      (@HDiv.hDiv Real Real Real c4
        c38
        c20)))

noncomputable def p14302 :=
BSN.rpow_neg_quarter_mk
  (@HDiv.hDiv Real Real Real c4
    (@OfScientific.ofScientific Real c2 101655800
      true 5)
    c7)

noncomputable def p14303 :=
p14302
  (BSN.t_div_two_pi_nonneg
    (@OfScientific.ofScientific Real c2 101655800
      true 5)
    101655800 100000
    (Enclosure.sfrac_ofScientific_eq 101655800 5 100000 (Eq.refl true)))

noncomputable def p14304 :=
@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt p14099)) false
  4817056930 17179869184 2 17179869184 2408528465 8589934592

noncomputable def p14305 :=
@Enclosure.Real.IsNear.recentre' (Real.sqrt p14099) false 61271417271
  17179869184 7 17179869184 61271417271 17179869184 7
  17179869184

noncomputable def p14306 :=
@Enclosure.Real.IsNear.sqrt_image
  (@HDiv.hDiv Real Real Real c4
    (@OfScientific.ofScientific Real c2 101655800
      true 5)
    c7)

noncomputable def p14307 :=
@Enclosure.Real.IsNear.of_eq
  (@HDiv.hDiv Real Real Real c4
    (@OfScientific.ofScientific Real c2 101655800
      true 5)
    c7)

noncomputable def p14308 :=
@p14307
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 101655800 100000)
    (@Inv.inv Real Real.instInv
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)))
  false 1389767499171737

noncomputable def p14309 :=
@p14308 8589934592000 508279 8589934592000
  (BSN.t_div_two_pi_mk
    (@OfScientific.ofScientific Real c2 101655800
      true 5)
    101655800 100000
    (Enclosure.sfrac_ofScientific_eq 101655800 5 100000 (Eq.refl true)))

noncomputable def p14310 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 101655800 100000)
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi))
  101655800 100000 0

noncomputable def p14311 :=
@p14310 1 2734261103 17179869184 1 17179869184
  1389767499171737 8589934592000 508279 8589934592000
  (Enclosure.Real.IsNear.const false 101655800 100000) d142

noncomputable def p14312 :=
@p14306 1389767499171737 8589934592000 508279 8589934592000
  109261209546 109261209587 8589934592
  (p14309 (p14311 (Eq.refl true))) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p14313 :=
@Enclosure.Real.IsNear.recentre' p14099 false 218522419133 17179869184
  41 17179869184 218522419133 17179869184 41 17179869184
  (p14312 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p14314 :=
@Enclosure.Real.IsNear.sqrt_image p14099 218522419133 17179869184 41
  17179869184 30635708632 30635708639 8589934592
  (p14313 (Eq.refl true)) (Eq.refl true) (Eq.refl true)

noncomputable def p14315 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt p14099) 61271417271 17179869184
  7 17179869184 2408528464 2408528466 8589934592
  (p14305
    (p14314 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p14316 :=
@p14301 (@Inv.inv Real Real.instInv (Real.sqrt p14099)) false
  2408528465 8589934592 1 8589934592 p14303
  (@p14304 1 8589934592
    (p14315 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p14317 :=
@Enclosure.Real.IsNear.addLit_ft_p
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
      (Enclosure.sfrac false 12 1)))
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Zeta.RiemannSiegel.correctionLinear
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
        (Enclosure.sfrac false 12 1)))
    (@Inv.inv Real Real.instInv p14099))
  69640417517939392135

noncomputable def p14318 :=
nat_lit
  99134189715291362463998604920188293227027672091675550313115707341287228070750600885442658662136938360420193577565230043689709765944954871429094359202102484385050555423420625

noncomputable def p14319 :=
nat_lit
  1436032001380675223115339185812105278919468554012329773482092409701700053992621646488797144419513484372699984661039038962002894730668802823836343146133308783017947416270411464172540909652143450656674541989538349144476975844459

noncomputable def p14320 :=
nat_lit
  1226898224389309775842895624992073707202658718620582696520316644359564669776917508045976509996635206780060977723177139190936316239060685816160844094362982809600000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p14321 :=
nat_lit
  8804156896601824383429163722517198781011089722406135746002273210306486117003251214010287970591970117653346248779309910714522727851309774247621751341706763068187925785167206207416335119040192184320

noncomputable def p14322 :=
@p14317 147573952589676412928 443766269906043779443 p9404
  p14318 p14295 p14319 p14320
  p14321 p14294 p14295 p14296

noncomputable def p14323 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  (@Inv.inv Real Real.instInv
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
          (Enclosure.sfrac false 12 1)))))

noncomputable def p14324 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
        (Enclosure.sfrac false 12 1))
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
        (Enclosure.sfrac false 12 1)))
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
      (Enclosure.sfrac false 12 1)))

noncomputable def p14325 :=
@Enclosure.Real.IsNear.of_eq
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
      (Enclosure.sfrac false 12 1)))
  (p14323
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p14324 (Enclosure.sfrac false 1 16)))))

noncomputable def p14326 :=
BSN.cos_two_pi_p_ne_zero_mk
  (@OfScientific.ofScientific Real c2 101655800
    true 5)
  101655800 100000 12
  (Enclosure.sfrac_ofScientific_eq 101655800 5 100000 (Eq.refl true))

noncomputable def p14327 :=
@Enclosure.Real.IsNear.mulLit_tt
  (@Inv.inv Real Real.instInv
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
          (Enclosure.sfrac false 12 1)))))

noncomputable def p14328 :=
@p14327
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p14324 (Enclosure.sfrac false 1 16))))
  90724586755

noncomputable def p14329 :=
@p14328 17179869184 7369 17179869184 767602477
  8589934592 8175311989 221459251200000000 69640417517939392135
  147573952589676412928 443766269906043779443 p9404

noncomputable def p14330 :=
@Enclosure.Real.IsNear.of_eq
  (@Inv.inv Real Real.instInv
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
          (Enclosure.sfrac false 12 1)))))

noncomputable def p14331 :=
@Inv.inv Real Real.instInv
  (@Neg.neg Real Real.instNeg
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
          (Enclosure.sfrac false 12 1)))))

noncomputable def p14332 :=
@p14330 (@Neg.neg Real Real.instNeg p14331) true 90724586755
  17179869184 7369 17179869184
  (BSN.inv_eq_neg_inv_neg
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
          (Enclosure.sfrac false 12 1)))))

noncomputable def p14333 :=
@Enclosure.Real.IsNear.inv_image
  (@Neg.neg Real Real.instNeg
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
          (Enclosure.sfrac false 12 1)))))

noncomputable def p14334 :=
@Enclosure.Real.IsNear.neg
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
        (Enclosure.sfrac false 12 1))))
  true

noncomputable def p14335 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
        (Enclosure.sfrac false 12 1))))
  true

noncomputable def p14336 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
      (Enclosure.sfrac false 12 1)))
  (@HDiv.hDiv Real Real Real c4
    (@Nat.cast Real Real.instNatCast 77685233551)
    (@Nat.cast Real Real.instNatCast 17179869184))
  false

noncomputable def p14337 :=
nat_lit 10933224652362066055628375

noncomputable def p14338 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
      (Enclosure.sfrac false 12 1)))
  false p14337

noncomputable def p14339 :=
nat_lit 1106429197976662025624321247

noncomputable def p14340 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
    (Enclosure.sfrac false 12 1))
  884279719003555 140737488355328 1

noncomputable def p14341 :=
@Enclosure.Real.IsNear.subLit_ff_p p14099 (Enclosure.sfrac false 12 1)
  218522419133 17179869184 41 17179869184 12 1 0

noncomputable def p14342 :=
@p14340 500000000000000 12363988925 17179869184 41
  17179869184 p14337 p2602 p14339
  p5018 d141
  (@p14341 1 12363988925 12363988925 17179869184 41
    17179869184 (p14313 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p14343 :=
@p14336 77685233551 17179869184 259 17179869184 true
  3253229535 17179869184 1 3300000000
  (@p14338 p2602 p14339 p5018
    77685233551 17179869184 259 17179869184
    (p14342 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div 77685233551 17179869184)

noncomputable def p14344 :=
nat_lit 3417415377911932610288812032

noncomputable def p14345 :=
BSN.cos_reduce2
  (@HDiv.hDiv Real Real Real c4
    (@Nat.cast Real Real.instNatCast 77685233551)
    (@Nat.cast Real Real.instNatCast 17179869184))
  (@HDiv.hDiv Real Real Real c4
    (@Nat.cast Real Real.instNatCast p14344)
    (@Nat.cast Real Real.instNatCast p2333))
  226375608064910080 72057594037927936 false

noncomputable def p14346 :=
BSN.sin_reduce_arg_pos_rat_q2 77685233551 17179869184 226375608064910080
  72057594037927936 0 p14344 p2333 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p14347 :=
nat_lit
  261296518641212186025655694535842339757029984143092835296532423292558632439016187298809287455957828499672877487564995079517584099105564302737356001979497794351367066053521

noncomputable def p14348 :=
nat_lit
  172113773305929025256783120359135922741052554978388774321640543906230234648436025786122017456957926523260426749664289129681020733846216778062797819577051697957399441

noncomputable def p14349 :=
nat_lit
  1582919669025174460749391120774142212058375038581604335943717383397148056380721261147868212355583337601890709928651798673400152588673496425155373749780143539444848444926865

noncomputable def p14350 :=
BSN.cos_dyadic_bound_f 48564393437003 35184372088832 4 3 17179869184
  6606445313 p14347 p2613 p14348
  p14349 p2616

noncomputable def p14351 :=
@BSN.binarySplit_of_base3 (BSN.cosEvenP 48564393437003) (BSN.cosEvenQ 35184372088832) 0
  3 p14347 p2613 p14348 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p14352 :=
p14350 p14348 3253229535 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p14351 (Eq.refl true))

noncomputable def p14353 :=
@BSN.binarySplit_of_base3 (BSN.cosOddP 48564393437003) (BSN.cosOddQ 35184372088832) 0
  3 p14349 p2616 p14348 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p14354 :=
@BSN.cos_arg_round false 3253229535 17179869184 p14344
  p2333 48564393437003 35184372088832 6606445313 6600000000
  (p14352 (p14353 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p14355 :=
p14345 3253229535 17179869184 0 1000000000000000
  6600000000 3300000000 p14346 BSN.pi_near_15 p14354
  (Eq.refl true) (Eq.refl true)

noncomputable def p14356 :=
@p14334 3253229535 17179869184 3405780739 221459251200000000
  (@p14335 3253229535 17179869184 871879869184
    56693568307200000000 3253229535 17179869184 3405780739
    221459251200000000
    (p14343 (p14355 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p14357 :=
@p14333 3253229535 17179869184 3405780739 221459251200000000
  45362289693 45362297062 8589934592 p14356
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p14358 :=
@Enclosure.Real.IsNear.recentre' p14331 false 90724586755 17179869184
  7369 17179869184 90724586755 17179869184 7369 17179869184
  (p14357 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p14359 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p14324 (Enclosure.sfrac false 1 16))))
  true

noncomputable def p14360 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p14324 (Enclosure.sfrac false 1 16)))
  (@HDiv.hDiv Real Real Real c4
    (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 14261665463))
    (@Nat.cast Real Real.instNatCast 8589934592))
  true

noncomputable def p14361 :=
nat_lit 68965182436552987403549200362744005

noncomputable def p14362 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p14324 (Enclosure.sfrac false 1 16)))
  true p14361

noncomputable def p14363 :=
nat_lit 46368061847193084192974236555906425597

noncomputable def p14364 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (p14324 (Enclosure.sfrac false 1 16)) 884279719003555
  140737488355328 1

noncomputable def p14365 :=
@Enclosure.Real.IsNear.subLit_tf
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
        (Enclosure.sfrac false 12 1))
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
        (Enclosure.sfrac false 12 1)))
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
      (Enclosure.sfrac false 12 1)))

noncomputable def p14366 :=
@p14365 (Enclosure.sfrac false 1 16) 59543490186402131575
  295147905179352825856 1718221730075 295147905179352825856 1 16
  0

noncomputable def p14367 :=
@Enclosure.Real.IsNear.subLit_ff_n
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
      (Enclosure.sfrac false 12 1))
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
      (Enclosure.sfrac false 12 1)))
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
    (Enclosure.sfrac false 12 1))
  152868222137522655625

noncomputable def p14368 :=
nat_lit 1022949372161176396077255884800

noncomputable def p14369 :=
@p14367 295147905179352825856 1013847093531 295147905179352825856
  12363988925 17179869184 41 17179869184 p14368
  59543490186402131575 295147905179352825856 1718221730075

noncomputable def p14370 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
    (Enclosure.sfrac false 12 1))
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
    (Enclosure.sfrac false 12 1))
  12363988925 17179869184 41

noncomputable def p14371 :=
@p14370 17179869184 12363988925 17179869184 41
  17179869184 152868222137522655625 295147905179352825856 1013847093531
  295147905179352825856
  (@p14341 1 12363988925 12363988925 17179869184 41
    17179869184 (p14313 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p14372 :=
p14371
  (@p14341 1 12363988925 12363988925 17179869184 41
    17179869184 (p14313 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p14373 :=
@p14369 295147905179352825856 (p14372 (Eq.refl true))
  (@p14341 1 12363988925 12363988925 17179869184 41
    17179869184 (p14313 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p14374 :=
@p14364 500000000000000 77990234260111683191 295147905179352825856
  1718221730075 295147905179352825856 p14361 p2630
  p14363 p2632 d141
  (@p14366 1 1247843748161786931056 77990234260111683191
    295147905179352825856 1718221730075 295147905179352825856
    (p14373 (Eq.refl true) (Eq.refl true))
    (Enclosure.Real.IsNear.const false 1 16) (Eq.refl true)
    (Eq.refl true))

noncomputable def p14375 :=
@p14360 14261665463 8589934592 629 17179869184 true
  767602477 8589934592 1 3300000000
  (@p14362 p2630 p14363 p2632
    14261665463 8589934592 629 17179869184
    (p14374 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_true_div 14261665463 8589934592)

noncomputable def p14376 :=
nat_lit
  5846940659673994368419740819392902535705561564586906994645051852647626226359369937696727924449136612252405536043839699834498456761420549032253331515307537726001131052872321

noncomputable def p14377 :=
nat_lit
  2929030670048364893776432969763411149463917344681527513330985807663341713346926356094087096319038932253422203846295556755929149236196861146649213817422385190810241

noncomputable def p14378 :=
nat_lit
  59459636523570487594385778613033837304363289615823908463968475909486875912244192883292591983691198554461240219808657294425123561932155633773588157772038790922202357372826241

noncomputable def p14379 :=
BSN.cos_dyadic_bound_t 14261665463 8589934592 5 4 8589934592
  3300000000 p14376 p2646 p14377
  p14378 p2649

noncomputable def p14380 :=
@BSN.binarySplit_of_base4 (BSN.cosEvenP 14261665463) (BSN.cosEvenQ 8589934592) 0
  4 p14376 p2646 p14377 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p14381 :=
p14379 p14377 767602477 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p14380 (Eq.refl true))

noncomputable def p14382 :=
@BSN.binarySplit_of_base4 (BSN.cosOddP 14261665463) (BSN.cosOddQ 8589934592) 0 4
  p14378 p2649 p14377 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p14383 :=
p14375
  (BSN.cos_neg_of_bound 14261665463 8589934592 true 767602477 8589934592
    1 3300000000
    (p14381 (p14382 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p14384 :=
p14329
  (p14332
    (@Enclosure.Real.IsNear.neg p14331 false 90724586755 17179869184
      7369 17179869184 (p14358 (Eq.refl true))))
  (@p14359 767602477 8589934592 2092879869184
    56693568307200000000 767602477 8589934592 8175311989
    221459251200000000 (p14383 (Eq.refl true)) (Eq.refl true))

noncomputable def p14385 :=
@p14322 p14297
  (@p14325 false 69640417517939392135 147573952589676412928
    443766269906043779443 p9404
    (BSN.correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
        (Enclosure.sfrac false 12 1))
      (p14326 (Eq.refl true) (Eq.refl true)
        (p14102 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p14384 (Eq.refl true)))

noncomputable def p14386 :=
nat_lit
  73397244467371487453644944778302948051260705127930977042597064681704865650534476117651290644759277752343511194333840445191343216753285369015478778153375377314359625

noncomputable def p14387 :=
nat_lit
  7371020360979572953596786290992712677572111758625860211672277930167234692172165726730716260112614780354430419981960634569864423105321860610471551272329484460252725248

noncomputable def p14388 :=
@Enclosure.Real.IsNear.mulLit_tf
  (Zeta.RiemannSiegel.correctionLinear
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
      (Enclosure.sfrac false 12 1)))
  (@Inv.inv Real Real.instInv p14099) p14386 p14387

noncomputable def p14389 :=
nat_lit
  1062686829763980078724430664112715723778344416627223218739047691984234140579552826107545712022332490227673924397861908743668137305759840884731787572654814816336930922494013332664714517800894466265308215137386382568979

noncomputable def p14390 :=
nat_lit
  71414875820588191030715570377190231066351914698059129093326432884179793168844044444033440085863415546485978278982053696581646581125718414327178854400000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p14391 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  (@iteratedDeriv Real c11 Real
    Real.normedAddCommGroup
    c8
    (@OfNat.ofNat Nat 3 (instOfNatNat 3)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
      (Enclosure.sfrac false 12 1)))
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 96 1)
      c16))

noncomputable def p14392 :=
@Enclosure.Real.IsNear.of_eq
  (Zeta.RiemannSiegel.correctionLinear
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
      (Enclosure.sfrac false 12 1)))
  (@Neg.neg Real Real.instNeg p14391) true p14386

noncomputable def p14393 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@iteratedDeriv Real c11 Real
    Real.normedAddCommGroup
    c8
    (@OfNat.ofNat Nat 3 (instOfNatNat 3)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
      (Enclosure.sfrac false 12 1)))
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 96 1)
      c16))

noncomputable def p14394 :=
nat_lit
  988259353587143724963406128386696669331246695217772797990191052059051665517844715730204871872571175529467071365675556635578562293865677075943281186290125

noncomputable def p14395 :=
nat_lit
  386328125867978897967601111750973983180428750077731476754872561582554347649746360691582798132590743459323430685027755066365763815741587730867648397797177394928557301021635988819199004550837210901236053949541

noncomputable def p14396 :=
nat_lit
  27401393469345423992384104397276249738858690773889698072022919289350602633117961204176579063845227604973635685787989044224907185173299200000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p14397 :=
@p14393 p14394 p2658 p14395
  p14396 74269213037 70368744177664 1 70368744177664
  p14386 p14387 p14389

noncomputable def p14398 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p14399 :=
p14398
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p14400 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p14399
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p14401 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p14400
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p14324 (Enclosure.sfrac false 1 16)))))

noncomputable def p14402 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  (Enclosure.sfrac false 3 1)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p14403 :=
p14401
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p14402
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 4 1) Real.pi))
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p14324 (Enclosure.sfrac false 1 16)))))

noncomputable def p14404 :=
@Neg.neg Real Real.instNeg
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
          (Enclosure.sfrac false 12 1)))))

noncomputable def p14405 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14403
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 3 1) p14404)
    (@iteratedDeriv Real c11 Real
      Real.normedAddCommGroup
      c10
      (@OfNat.ofNat Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
        (Enclosure.sfrac false 12 1))))

noncomputable def p14406 :=
@Neg.neg Real Real.instNeg
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 4 1)
      c16)
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
          (Enclosure.sfrac false 12 1)))))

noncomputable def p14407 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14405
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 3 1) p14406)
    (@iteratedDeriv Real c11 Real
      Real.normedAddCommGroup
      c10
      (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
        (Enclosure.sfrac false 12 1))))

noncomputable def p14408 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 8 1)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      c16 Real.pi))
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
        (Enclosure.sfrac false 12 1))))

noncomputable def p14409 :=
@Enclosure.Real.IsNear.of_eq
  (@iteratedDeriv Real c11 Real
    Real.normedAddCommGroup
    c8
    (@OfNat.ofNat Nat 3 (instOfNatNat 3)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
      (Enclosure.sfrac false 12 1)))
  (p14323
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14407
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p14408
        (Zeta.RiemannSiegel.correction
          (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
            (Enclosure.sfrac false 12 1))))))

noncomputable def p14410 :=
@p14327
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14407
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p14408
      (Zeta.RiemannSiegel.correction
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
          (Enclosure.sfrac false 12 1)))))
  371607888103645

noncomputable def p14411 :=
nat_lit
  2659414359125521909566788878468712257319890403693079725744201113094493680799278184815505542786993002547107346700564697611581738571473186225

noncomputable def p14412 :=
nat_lit
  1488565707357402911845015158554633286356257506687627387456491927921949262056238946972039271861787782268441644249633132407878864135402815488

noncomputable def p14413 :=
nat_lit
  1039598490091658672604191897306078767747191765379213698360785067668964645115629629006055652227652259475865362840223716071815242773711126054931525726855257824024240996074956588540935855680259369

noncomputable def p14414 :=
nat_lit
  389397221586952809849209762621686788561116412294747108149165900518804088408131195879158483760494783680508642274105412812800000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p14415 :=
@p14410 70368744177664 7369 70368744177664 p14411
  p14412 p14413 p14414 p14394
  p2658 p14395 p14396

noncomputable def p14416 :=
@p14330 (@Neg.neg Real Real.instNeg p14331) true 371607888103645
  70368744177664 7369 70368744177664
  (BSN.inv_eq_neg_inv_neg
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
          (Enclosure.sfrac false 12 1)))))

noncomputable def p14417 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
      (Enclosure.sfrac false 12 1)))
  (@HDiv.hDiv Real Real Real c4
    c60
    c61)
  false

noncomputable def p14418 :=
nat_lit 44782488076875639406316020545

noncomputable def p14419 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
      (Enclosure.sfrac false 12 1)))
  false p14418

noncomputable def p14420 :=
nat_lit 221372822191336326834729619

noncomputable def p14421 :=
nat_lit 60446290980731458735308800000000000000

noncomputable def p14422 :=
@Enclosure.Real.IsNear.subLit_ff_p p14099 (Enclosure.sfrac false 12 1)
  895067828656587 70368744177664 41 70368744177664 12 1
  0

noncomputable def p14423 :=
@p14307
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 101655800 100000)
    (@Inv.inv Real Real.instInv
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)))
  false 1138497535032479511

noncomputable def p14424 :=
@p14423 7036874417766400 508279 35184372088832000
  (BSN.t_div_two_pi_mk
    (@OfScientific.ofScientific Real c2 101655800
      true 5)
    101655800 100000
    (Enclosure.sfrac_ofScientific_eq 101655800 5 100000 (Eq.refl true)))

noncomputable def p14425 :=
@p14310 1 11199533475045 70368744177664 1
  70368744177664 1138497535032479511 7036874417766400 508279
  35184372088832000 (Enclosure.Real.IsNear.const false 101655800 100000)
  d198

noncomputable def p14426 :=
@p14306 1138497535032479511 7036874417766400 508279
  35184372088832000 447533914328273 447533914328314 35184372088832
  (p14424 (p14425 (Eq.refl true))) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p14427 :=
@Enclosure.Real.IsNear.recentre' p14099 false 895067828656587 70368744177664
  41 70368744177664 895067828656587 70368744177664 41
  70368744177664
  (p14426 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p14428 :=
@p14340 500000000000000 50642898524619 70368744177664 41
  70368744177664 p14418 p12189 p14420
  p14421 d197
  (@p14422 1 50642898524619 50642898524619 70368744177664
    41 70368744177664 (p14427 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p14429 :=
@p14417 39774839490359 8796093022208 259 70368744177664
  true 13325228865326 70368744177664 1 13516800000000
  (@p14419 p12189 p14420 p14421
    39774839490359 8796093022208 259 70368744177664
    (p14428 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div 39774839490359 8796093022208)

noncomputable def p14430 :=
nat_lit 1749716660844369397247291424768

noncomputable def p14431 :=
nat_lit 1267650600228229401496703205376

noncomputable def p14432 :=
BSN.cos_reduce2
  (@HDiv.hDiv Real Real Real c4
    c60
    c61)
  (@HDiv.hDiv Real Real Real c4
    (@Nat.cast Real Real.instNatCast p14430)
    (@Nat.cast Real Real.instNatCast p14431))
  226375608064910080 72057594037927936 false

noncomputable def p14433 :=
BSN.sin_reduce_arg_pos_rat_q2 39774839490359 8796093022208 226375608064910080
  72057594037927936 0 p14430 p14431
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p14434 :=
nat_lit
  109792993845290667253282785485439062894141175478851655051725442477399052416702080849065858849281655539711056531698162814048711057418341265781532487720870663355316263545599933575184048898821101739567131179929672012333949062462123670080624317366872473859815602285254482699086591438069170176

noncomputable def p14435 :=
nat_lit
  6009614559827576751214090175326788067604329498546018318988401207202051756928782168974017856895601250144584333662684034211288119030605688977694319785133976017638270956480849973129188768458289492679796358517930761567035595911765426603371561081411175167592468129428609141357674496

noncomputable def p14436 :=
nat_lit
  1118278353150697705181007511380504479657667507049821482809746747258618727657257566860207329827373449767138606333991736614542931959011209264634460371557163834807913109781602064882706906260611066667504337920349268190115984583019484480815252384619066014410443786643137372939471590660973264896

noncomputable def p14437 :=
BSN.cos_dyadic_bound_f 198919754080221696 144115188075855872 5 4
  70368744177664 27060000000001 p14434 p12205
  p14435 p14436 p12208

noncomputable def p14438 :=
@BSN.binarySplit_of_base4 (BSN.cosEvenP 198919754080221696) (BSN.cosEvenQ 144115188075855872)
  0 4 p14434 p12205 p14435
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p14439 :=
p14437 p14435 13325228865326 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p14438 (Eq.refl true))

noncomputable def p14440 :=
@BSN.binarySplit_of_base4 (BSN.cosOddP 198919754080221696) (BSN.cosOddQ 144115188075855872)
  0 4 p14436 p12208 p14435
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p14441 :=
@BSN.cos_arg_round false 13325228865326 70368744177664 p14430
  p14431 198919754080221696 144115188075855872 27060000000001
  27033600000000
  (p14439 (p14440 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p14442 :=
p14432 13325228865326 70368744177664 0 1000000000000000
  27033600000000 13516800000000 p14433 BSN.pi_near_15 p14441
  (Eq.refl true) (Eq.refl true)

noncomputable def p14443 :=
@p14334 6662614432663 35184372088832 3405780739
  907097092915200000000
  (@p14335 13325228865326 70368744177664 3571219944177664
    p4996 6662614432663 35184372088832 3405780739
    907097092915200000000
    (p14429 (p14442 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p14444 :=
@p14333 6662614432663 35184372088832 3405780739
  907097092915200000000 185803944048138 185803944055507 35184372088832
  p14443 (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p14445 :=
@Enclosure.Real.IsNear.recentre' p14331 false 371607888103645 70368744177664
  7369 70368744177664 371607888103645 70368744177664 7369
  70368744177664
  (p14444 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p14446 :=
nat_lit
  173751414142576841804405131186107225015093485358760696803944895438842443697195655401428817335617183693134596886952247983215685438165426466225

noncomputable def p14447 :=
@Enclosure.Real.IsNear.subLit_tt_n p14407
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p14408
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
        (Enclosure.sfrac false 12 1))))
  p14446 p14412

noncomputable def p14448 :=
nat_lit
  1034025820103467292730397560508050816205151042457913787270590537786578068997443926372144156062704096935243342324453846561876236449418680807576466457300763642577889987304390198780935855680259369

noncomputable def p14449 :=
nat_lit 13955342382821968606181538459151056045911796937305454785565874840452665138805062956875

noncomputable def p14450 :=
nat_lit
  8206300653128271494860075583174038895062555007459510600211687100731186461863429507119504379236624836241881313059130569809

noncomputable def p14451 :=
nat_lit
  573425428135293881570163660737585503976383794455989910779723272683520000000000000000000000000000000000000000000000000000000000000

noncomputable def p14452 :=
nat_lit
  322897596688223429340944888882454382973046378147743926403886824481190951815273753426497811717997545094062167332755609454611223083472577248222790529341774338587747692625745337824630072100763909589402802835908644130363801600

noncomputable def p14453 :=
@p14447 p14448 p14414 p14449
  p12222 p14450 p14451 p14452
  p14411 p14412 p14413 p14414

noncomputable def p14454 :=
@Enclosure.Real.IsNear.subLit_tf p14405
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 3 1) p14406)
    (@iteratedDeriv Real c11 Real
      Real.normedAddCommGroup
      c10
      (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
        (Enclosure.sfrac false 12 1))))

noncomputable def p14455 :=
nat_lit
  145212452153821472514076176713585166465565456737261156684138006987824936430082459057770817000460770352260749884582935364588549002583023906225

noncomputable def p14456 :=
nat_lit
  1015528048479918704848528021246694536411072854543634312796710777994673365285231691826762245090734084699325580535532972583159350516697450284909679689776849717933570406773049455303533846080259369

noncomputable def p14457 :=
nat_lit 5763397475460507636656544388476144590110178302404399902221829234494728694033382882876449351529224992189430906875

noncomputable def p14458 :=
nat_lit 300613450595050653169853516389035139504087366260264943450533244356122755214669880763353471793250393988087676928

noncomputable def p14459 :=
nat_lit
  289791629970320722862386881616419730894839414367373196928420478830146650530796491080392464355237326437054464305517238390994665181343242790534210524845773707

noncomputable def p14460 :=
nat_lit
  6100413490127702206852427725363985247808884971931062586592581610704033397466252600842729291776000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p14461 :=
nat_lit
  52232012151169708779652525171631464091201159508558288268580794948165531795245179582022096691923001308811315214168866683689520546733080815341158973276087617590521472066014050493763938384001021464253750109778935769766189580179520088656503603668503756800

noncomputable def p14462 :=
@p14454 p14455 p14412 p14456
  p14414 p14457 p14458 p14459
  p14460 p14461 p14446 p14412

noncomputable def p14463 :=
@Enclosure.Real.IsNear.subLit_tf p14403
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 3 1) p14404)
    (@iteratedDeriv Real c11 Real
      Real.normedAddCommGroup
      c10
      (@OfNat.ofNat Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
        (Enclosure.sfrac false 12 1))))

noncomputable def p14464 :=
nat_lit 12445868091577256263591010704286946548570966181841559111877851165475106514170183075922090295337975

noncomputable def p14465 :=
nat_lit
  172030354360337935815342558584553104846521514647343581194363353055406687298168749912291593867148292052137074342796238781686311

noncomputable def p14466 :=
nat_lit
  130428209316912962525110357513786059405923310727377531334045022626513349226423910400000000000000000000000000000000000000000000000000000

noncomputable def p14467 :=
nat_lit
  127865443836022285795814643431211951805845406846025916873097949460302667878601093596526414548898080214056896339323375704577695500480120712625

noncomputable def p14468 :=
nat_lit
  1015014446841382308877069069178046857883662731710528799198443154310796596725635683443809664976008306903940024398726293513629374356386308733910929837935205654653497653621049455303533846080259369

noncomputable def p14469 :=
nat_lit
  155085957627424051136217223967876236405792880748375213867721844213776127064174229773831699165144766595094406164449902547759793411220665749724007431110592200414780351008668720320048379579627733744341223187689689890521455733996291673292800

noncomputable def p14470 :=
@p14463 p14464 p12373 p14465
  p14466 p14467 p14412 p14468
  p14414 p14469 p14455 p14412

noncomputable def p14471 :=
@Enclosure.Real.IsNear.subLit_tt_n
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p14400
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p14324 (Enclosure.sfrac false 1 16)))))

noncomputable def p14472 :=
@p14471
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p14402
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 4 1) Real.pi))
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p14324 (Enclosure.sfrac false 1 16)))))

noncomputable def p14473 :=
nat_lit 22378044479150695951849749830132261031458938228357532323859551597393601855041144267491857196688375

noncomputable def p14474 :=
nat_lit
  46477312431013255805686048272779614156179711550072430537641943845440135715145858601819405202670034473746226854796238781686311

noncomputable def p14475 :=
nat_lit 28503948327546614096820314555680393031288135842742502225

noncomputable def p14476 :=
nat_lit 3064991081731777716716694054300618367237478244367204352

noncomputable def p14477 :=
nat_lit 23613902642635993381258856593160491959012524882254426633424003728156219347

noncomputable def p14478 :=
nat_lit 24530819718383685455689290099913197656578457600000000000000000000000000000000000000

noncomputable def p14479 :=
nat_lit
  38146474705094390604969395928375546997701315992751980559940744615253382830254979588847955964172276857532042832928493860407037335848466658900969730867200

noncomputable def p14480 :=
@p14472 p14473 p12373 p14474
  p14466 p14475 p14476 p14477
  p14478 p14479 p14464 p12373

noncomputable def p14481 :=
nat_lit 2554308053474756177414593965648494890213425206074191201337082082477425422497809586625

noncomputable def p14482 :=
@Enclosure.Real.IsNear.mulLit_ft p14400
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p14324 (Enclosure.sfrac false 1 16))))
  p14481

noncomputable def p14483 :=
nat_lit 577713617827694958954605611805431409638043307281075681158448291661553753855183203957165733610123746684651

noncomputable def p14484 :=
nat_lit
  3450873173395281893717377931138512726225554486085193277581262111899648000000000000000000000000000000000000000000000

noncomputable def p14485 :=
@p14482 p12222 p14483 p14484
  8760902761399 8796093022208 8175311989 907097092915200000000
  p14473 p12373 p14474 p14466

noncomputable def p14486 :=
@Enclosure.Real.IsNear.mulLit_ff p14399
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p14487 :=
nat_lit 186859643141871541094759561099918118650480127028873156225

noncomputable def p14488 :=
nat_lit 923237684641888234189691322100158261114054448978644846812159189351

noncomputable def p14489 :=
nat_lit 22835963083295358096932575511191922182123945984000000000000000000000000000000

noncomputable def p14490 :=
nat_lit 13669661412846754965332222785

noncomputable def p14491 :=
nat_lit 1106561879501777976879971551

noncomputable def p14492 :=
nat_lit 151115727451828646838272000000000000000

noncomputable def p14493 :=
@p14486 p14487 p12261 p14488
  p14489 p14490 p12265 p14491
  p14492 p14481 p12222 p14483

noncomputable def p14494 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p14495 :=
@p14494
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p14496 :=
@p14495 p14490 p12265 p14491
  p14492 p14490 p12265 p14491
  p14492 p14487 p12261 p14488

noncomputable def p14497 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
        (Enclosure.sfrac false 12 1)))
    (Enclosure.sfrac false 1 1))
  884279719003555

noncomputable def p14498 :=
@p14497 140737488355328 1 500000000000000 15458526435787
  35184372088832 41 35184372088832 p14490 p12265
  p14491 p14492

noncomputable def p14499 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
      (Enclosure.sfrac false 12 1)))
  (Enclosure.sfrac false 1 1) 50642898524619 35184372088832

noncomputable def p14500 :=
@p14499 41 35184372088832 1 1 0 1
  15458526435787 15458526435787 35184372088832 41 35184372088832

noncomputable def p14501 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 2 1)
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
    (Enclosure.sfrac false 12 1))
  2 1 0 1

noncomputable def p14502 :=
@p14501 50642898524619 70368744177664 41 70368744177664
  50642898524619 35184372088832 41 35184372088832
  (Enclosure.Real.IsNear.const false 2 1)
  (@p14422 1 50642898524619 50642898524619 70368744177664
    41 70368744177664 (p14427 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p14503 :=
@p14496 p14489
  (p14498 d197
    (p14500 (p14502 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (p14498 d197
    (p14500 (p14502 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))

noncomputable def p14504 :=
@p14493 p14484 (p14503 (Eq.refl true))
  (p14498 d197
    (p14500 (p14502 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p14505 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p14324 (Enclosure.sfrac false 1 16))))
  true

noncomputable def p14506 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p14324 (Enclosure.sfrac false 1 16)))
  (@HDiv.hDiv Real Real Real c4
    (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 116831563784011))
    c35)
  true

noncomputable def p14507 :=
nat_lit 1157043765284408350152033740640651022463605

noncomputable def p14508 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p14324 (Enclosure.sfrac false 1 16)))
  true p14507

noncomputable def p14509 :=
nat_lit 189934817725369163675094582946549473646433

noncomputable def p14510 :=
nat_lit 1308459009540799813789595911

noncomputable def p14511 :=
nat_lit 998973999719454745064814855

noncomputable def p14512 :=
@p14365 (Enclosure.sfrac false 1 16) p14511
  p12265 7037836190304663 p12265 1 16 0

noncomputable def p14513 :=
nat_lit 20935344152652797020633534576

noncomputable def p14514 :=
nat_lit 2564703170974857286949095161

noncomputable def p14515 :=
@Enclosure.Real.IsNear.subLit_ff_n
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
      (Enclosure.sfrac false 12 1))
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
      (Enclosure.sfrac false 12 1)))
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
    (Enclosure.sfrac false 12 1))
  p14514

noncomputable def p14516 :=
nat_lit 70296545826396099461208427766087386398720

noncomputable def p14517 :=
@p14515 p12265 4152717679020439 p12265
  50642898524619 70368744177664 41 70368744177664 p14516
  p14511 p12265 7037836190304663

noncomputable def p14518 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
    (Enclosure.sfrac false 12 1))
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
    (Enclosure.sfrac false 12 1))
  50642898524619 70368744177664 41

noncomputable def p14519 :=
@p14518 70368744177664 50642898524619 70368744177664 41
  70368744177664 p14514 p12265 4152717679020439
  p12265
  (@p14422 1 50642898524619 50642898524619 70368744177664
    41 70368744177664 (p14427 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p14520 :=
p14519
  (@p14422 1 50642898524619 50642898524619 70368744177664
    41 70368744177664 (p14427 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p14521 :=
@p14517 p12265 (p14520 (Eq.refl true))
  (@p14422 1 50642898524619 50642898524619 70368744177664
    41 70368744177664 (p14427 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p14522 :=
@p14364 500000000000000 p14510 p12265
  7037836190304663 p12265 p14507 p12284
  p14509 p12286 d197
  (@p14512 1 p14513 p14510 p12265
    7037836190304663 p12265
    (p14521 (Eq.refl true) (Eq.refl true))
    (Enclosure.Real.IsNear.const false 1 16) (Eq.refl true)
    (Eq.refl true))

noncomputable def p14523 :=
@p14506 116831563784011 70368744177664 629 70368744177664
  true 35043611045596 35184372088832 1 13516800000000
  (@p14508 p12284 p14509 p12286
    116831563784011 70368744177664 629 70368744177664
    (p14522 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_true_div 116831563784011 70368744177664)

noncomputable def p14524 :=
nat_lit
  8161612991788335542584548072121726671389117816636330511001044519344854676274997475461096871517162455278555339763951015400283639963231775127631641218474056437593040927521825767881656167045071436693571142392045461773164189131058329548481

noncomputable def p14525 :=
nat_lit
  1204933380363112914166985584610140987945114304603371054272030990847611855191977010950523059826100763588166015008939361880258045512457226581003764967168294240045631476603449526482217489966945089362628882847121571671091517716161

noncomputable def p14526 :=
nat_lit
  66355817798805606822352665655324413138048458626718392092020812713856766573973453981268314159093865345380576020835795750610426856217775756658745891819561233072981072809047775522606450360435237420657439226730300531604608068028734659753665

noncomputable def p14527 :=
BSN.sin_dyadic_bound_f 116831563784011 70368744177664 5 4
  35184372088832 13516800000000 p14524 p13914
  p14525 p14526 p13917

noncomputable def p14528 :=
@BSN.binarySplit_of_base4 (BSN.sinEvenP 116831563784011) (BSN.sinEvenQ 70368744177664) 0
  4 p14524 p13914 p14525 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p14529 :=
p14527 p14525 35043611045596 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p14528 (Eq.refl true))

noncomputable def p14530 :=
@BSN.binarySplit_of_base4 (BSN.sinOddP 116831563784011) (BSN.sinOddQ 70368744177664) 0
  4 p14526 p13917 p14525 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p14531 :=
p14523
  (BSN.sin_neg_of_bound 116831563784011 70368744177664 false 35043611045596
    35184372088832 1 13516800000000
    (p14529 (p14530 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p14532 :=
p14485 p14504
  (@p14505 35043611045596 35184372088832 8572435944177664
    p4996 8760902761399 8796093022208 8175311989
    907097092915200000000 (p14531 (Eq.refl true))
    (Eq.refl true))

noncomputable def p14533 :=
nat_lit 36263413059077601351385508759600860401002025

noncomputable def p14534 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p14402
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 4 1) Real.pi))
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p14324 (Enclosure.sfrac false 1 16))))
  p14533

noncomputable def p14535 :=
nat_lit 89596037234189700465141858877994625437310986574173451

noncomputable def p14536 :=
nat_lit 324518553658426726783156020576256000000000000000000000000000000

noncomputable def p14537 :=
@p14534 p12314 p14535 p14536
  786024974569 8796093022208 8175311989 907097092915200000000
  p14475 p14476 p14477 p14478

noncomputable def p14538 :=
nat_lit 41008984238540264895996668355

noncomputable def p14539 :=
nat_lit 3319685638505333930639914653

noncomputable def p14540 :=
@Enclosure.Real.IsNear.mulLit_ff p14402
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 4 1) Real.pi)
  p14538 p12265 p14539 p14492

noncomputable def p14541 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 3 1)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p14542 :=
@p14541 3 1 0 1 p14490
  p12265 p14491 p14492 p14538
  p12265 p14539

noncomputable def p14543 :=
@p14542 p14492 (Enclosure.Real.IsNear.const false 3 1)
  (p14498 d197
    (p14500 (p14502 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p14544 :=
@p14540 884279719003555 70368744177664 1 250000000000000
  p14533 p12314 p14535 p14536
  p14543 d199 (Eq.refl true)

noncomputable def p14545 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p14324 (Enclosure.sfrac false 1 16)))
  (@HDiv.hDiv Real Real Real c4
    (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 116831563784011))
    c35)
  true

noncomputable def p14546 :=
@p14545 116831563784011 70368744177664 629 70368744177664
  true 3144099898276 35184372088832 1 13516800000000
  (@p14508 p12284 p14509 p12286
    116831563784011 70368744177664 629 70368744177664
    (p14522 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_true_div 116831563784011 70368744177664)

noncomputable def p14547 :=
nat_lit
  2405291901206112972387593418577166098867684327850674315090025561527620415948385063766711797862750976145409309686782894585781055973280147704464308944455702149304820191428071801144264934720620475438042856760565964320527859427113643407041

noncomputable def p14548 :=
nat_lit
  24460275979986491586187595534720316054899230738478796547065838149223333195268569028947337265655884368377001847408919216475130295820828291140080238388834926766972788539020689413907971717274622595369408182610727239139470778257361305466561

noncomputable def p14549 :=
BSN.cos_dyadic_bound_t 116831563784011 70368744177664 5 4
  35184372088832 13516800000000 p14547 p13938
  p14525 p14548 p13940

noncomputable def p14550 :=
@BSN.binarySplit_of_base4 (BSN.cosEvenP 116831563784011) (BSN.cosEvenQ 70368744177664) 0
  4 p14547 p13938 p14525 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p14551 :=
p14549 p14525 3144099898276 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p14550 (Eq.refl true))

noncomputable def p14552 :=
@BSN.binarySplit_of_base4 (BSN.cosOddP 116831563784011) (BSN.cosOddQ 70368744177664) 0
  4 p14548 p13940 p14525 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p14553 :=
p14546
  (BSN.cos_neg_of_bound 116831563784011 70368744177664 true 3144099898276
    35184372088832 1 13516800000000
    (p14551 (p14552 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p14554 :=
p14537 p14544
  (@p14359 3144099898276 35184372088832 8572435944177664
    p4996 786024974569 8796093022208 8175311989
    907097092915200000000 (p14553 (Eq.refl true))
    (Eq.refl true))

noncomputable def p14555 :=
nat_lit 183299445942681567846037968165

noncomputable def p14556 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 3 1) p14404)
  (@iteratedDeriv Real c11 Real
    Real.normedAddCommGroup
    c8
    (@OfNat.ofNat Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
      (Enclosure.sfrac false 12 1)))
  p14555

noncomputable def p14557 :=
nat_lit 91916306776432654999797381399126613

noncomputable def p14558 :=
nat_lit 697576815785936937221390948683046598608553855341830533348175722369584836212870390267655832014939012330273504925

noncomputable def p14559 :=
nat_lit 150306725297525326584926758194517569752043683130132471725266622178061377607334940381676735896625196994043838464

noncomputable def p14560 :=
nat_lit
  42223434262243669547383088805927754060254032719064229680138656115879418343121844482913375991954406465609460932396144257308073734666002449600265563

noncomputable def p14561 :=
nat_lit
  299847523866756818871210527557090602900302314140355588256198571329324649552261247836621830149373952000000000000000000000000000000000000000000000000000000

noncomputable def p14562 :=
@p14556 p12189 p14557 p13950
  p14558 p14559 p14560 p14561
  p14467 p14412 p14468 p14414

noncomputable def p14563 :=
nat_lit 61099815314227189282012656055

noncomputable def p14564 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 3 1) p14404
  3 1 0 1 p14563 p12189

noncomputable def p14565 :=
@Enclosure.Real.IsNear.neg
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
          (Enclosure.sfrac false 12 1)))))

noncomputable def p14566 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
        (Enclosure.sfrac false 12 1))))
  884279719003555

noncomputable def p14567 :=
@p14566 140737488355328 1 500000000000000 69095574625501
  70368744177664 3405780739 907097092915200000000 p14563
  p12189 p14557 p13957

noncomputable def p14568 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
        (Enclosure.sfrac false 12 1))))
  true

noncomputable def p14569 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
      (Enclosure.sfrac false 12 1)))
  (@HDiv.hDiv Real Real Real c4
    c60
    c61)
  false

noncomputable def p14570 :=
@p14569 39774839490359 8796093022208 259 70368744177664
  true 69095574625501 70368744177664 1 13516800000000
  (@p14419 p12189 p14420 p14421
    39774839490359 8796093022208 259 70368744177664
    (p14428 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div 39774839490359 8796093022208)

noncomputable def p14571 :=
BSN.sin_reduce2
  (@HDiv.hDiv Real Real Real c4
    c60
    c61)
  (@HDiv.hDiv Real Real Real c4
    (@Nat.cast Real Real.instNatCast p14430)
    (@Nat.cast Real Real.instNatCast p14431))
  226375608064910080 72057594037927936 false

noncomputable def p14572 :=
nat_lit
  372938345978389546689587166185669491915760443196713034264717872040572676077213197346255069942994923035190067568771863777588445063646799722624210563322291652151517108896550727513574909387639301063416498045175211597091572331793299281018430847309851692558101155984855632289296916841041494016

noncomputable def p14573 :=
nat_lit
  3034532450288191570469937624144785129640388909187003725544258845658583526548588262396166322422978103000958127661107203027475962632345475130960105838203134734373256912751188581638574612606616694477156285735683783904522363672628060037618023277836652479797484175823958826324969662361464995840

noncomputable def p14574 :=
BSN.sin_dyadic_bound_f 198919754080221696 144115188075855872 5 4
  70368744177664 27060000000001 p14572 p12357
  p14435 p14573 p12359

noncomputable def p14575 :=
@BSN.binarySplit_of_base4 (BSN.sinEvenP 198919754080221696) (BSN.sinEvenQ 144115188075855872)
  0 4 p14572 p12357 p14435
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p14576 :=
p14574 p14435 69095574625501 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p14575 (Eq.refl true))

noncomputable def p14577 :=
@BSN.binarySplit_of_base4 (BSN.sinOddP 198919754080221696) (BSN.sinOddQ 144115188075855872)
  0 4 p14573 p12359 p14435
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p14578 :=
@BSN.sin_arg_round false 69095574625501 70368744177664 p14430
  p14431 198919754080221696 144115188075855872 27060000000001
  27033600000000
  (p14576 (p14577 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p14579 :=
p14571 69095574625501 70368744177664 0 1000000000000000
  27033600000000 13516800000000 p14433 BSN.pi_near_15 p14578
  (Eq.refl true) (Eq.refl true)

noncomputable def p14580 :=
p14567 d197
  (@p14568 69095574625501 70368744177664 3571219944177664
    p4996 69095574625501 70368744177664 3405780739
    907097092915200000000
    (p14570 (p14579 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p14581 :=
@Neg.neg Real Real.instNeg
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p14399
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p14324 (Enclosure.sfrac false 1 16)))))

noncomputable def p14582 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14581
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 4 1) Real.pi)
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p14324 (Enclosure.sfrac false 1 16)))))

noncomputable def p14583 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14582
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) p14404)
    (@iteratedDeriv Real c11 Real
      Real.normedAddCommGroup
      c10
      (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
        (Enclosure.sfrac false 12 1))))

noncomputable def p14584 :=
@Enclosure.Real.IsNear.of_eq
  (@iteratedDeriv Real c11 Real
    Real.normedAddCommGroup
    c8
    (@OfNat.ofNat Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
      (Enclosure.sfrac false 12 1)))
  (p14323
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14583
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p14406
        (Zeta.RiemannSiegel.correction
          (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
            (Enclosure.sfrac false 12 1))))))

noncomputable def p14585 :=
@p14327
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14583
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p14406
      (Zeta.RiemannSiegel.correction
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
          (Enclosure.sfrac false 12 1)))))
  371607888103645

noncomputable def p14586 :=
nat_lit 1877185167800787050313308674581535580944262948624121778701394574853800723148665278916018109878465

noncomputable def p14587 :=
nat_lit 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576

noncomputable def p14588 :=
nat_lit
  113549362504769053954234763869757184290824204269176957124046913304628589177501129409773773921347358313578063454555325302583654620567

noncomputable def p14589 :=
nat_lit
  4261089598383546485695355379975390560791514561463423948683250889208191119227269152768000000000000000000000000000000000000000000000000000000

noncomputable def p14590 :=
@p14585 70368744177664 7369 70368744177664 p14586
  p14587 p14588 p14589 p14558
  p14559 p14560 p14561

noncomputable def p14591 :=
nat_lit 5658190020856479492294542384543219131822269674491929696553710634760511394872944438308134388297535

noncomputable def p14592 :=
@Enclosure.Real.IsNear.subLit_ff_n p14583
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p14406
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
        (Enclosure.sfrac false 12 1))))
  p14591 p14587

noncomputable def p14593 :=
nat_lit
  111437095880628682223057842478000367477519319755047543754123519962309073890205836328145231055787915287213919284805136464490854620567

noncomputable def p14594 :=
nat_lit 1521756900481055716999100842712984076684339880790576060729118061352875

noncomputable def p14595 :=
nat_lit 264731212126022509448371945657972539657709257220399126572273381018289201924577915201085875954383

noncomputable def p14596 :=
nat_lit
  809740992132407093524808389270021187869381704847183218460594840662170711397547842173325935733616928976194321246560101736390290282710643243782675523528672481944535040

noncomputable def p14597 :=
@p14592 p14593 p14589 p14594
  p12388 p14595 p13990 p14596
  p14586 p14587 p14588 p14589

noncomputable def p14598 :=
@Enclosure.Real.IsNear.subLit_ff_p p14582
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) p14404)
    (@iteratedDeriv Real c11 Real
      Real.normedAddCommGroup
      c10
      (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
        (Enclosure.sfrac false 12 1))))

noncomputable def p14599 :=
nat_lit 2846342746469932711503580387753312063054614372408720738367075373024105

noncomputable def p14600 :=
nat_lit 215679573337205118357336120696157045389097155380324579848828881993728

noncomputable def p14601 :=
nat_lit 480458838682752478562433556778788627203718561981268510383978038096398465583857860579033

noncomputable def p14602 :=
nat_lit 2589304465847005815082263137073162396642221620841414236569600000000000000000000000000000000000000

noncomputable def p14603 :=
nat_lit 22530623190220686016912143191322636622721240770563744011289521886146019956242015285088497143058625

noncomputable def p14604 :=
nat_lit
  110646428662089430534241293725007528412324375171119491357393946744727595132734923778724203731762828040322131390676496464490854620567

noncomputable def p14605 :=
nat_lit
  1220356009559157226852550992207006863738377865774940758594323861011682210928961383284534780635929509947114531251850795181308354175287877666176102420046898522467860480

noncomputable def p14606 :=
@p14598 p14599 p14600 p14601
  p14602 p14603 p14587 p14604
  p14589 p14605 p14591 p14587

noncomputable def p14607 :=
@Enclosure.Real.IsNear.subLit_ft p14581
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 4 1) Real.pi)
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p14324 (Enclosure.sfrac false 1 16)))))

noncomputable def p14608 :=
nat_lit 146876346248561993348073222432732740880225966447509912150482389042025

noncomputable def p14609 :=
nat_lit 62398264333384775118742657081023911913178072272075529689358913134865792527952620193011

noncomputable def p14610 :=
nat_lit 863101488615668605027421045691054132214073873613804745523200000000000000000000000000000000000000

noncomputable def p14611 :=
nat_lit 7747088632067376776197773445

noncomputable def p14612 :=
nat_lit 220627346559477365577921533135845363

noncomputable def p14613 :=
nat_lit 1761800825692322844325417848491615984658969402815979606740202032556658209444684982712289470709760

noncomputable def p14614 :=
@p14607 p14608 p14600 p14609
  p14610 p14611 p504 p14612
  p12348 p14613 p14599 p14600

noncomputable def p14615 :=
@Enclosure.Real.IsNear.neg
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p14399
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p14324 (Enclosure.sfrac false 1 16)))))

noncomputable def p14616 :=
@Enclosure.Real.IsNear.mulLit_ft p14399
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p14324 (Enclosure.sfrac false 1 16))))
  p14487

noncomputable def p14617 :=
@p14616 p12261 p14488 p14489
  786024974569 8796093022208 8175311989 907097092915200000000
  p14608 p14600 p14609 p14610

noncomputable def p14618 :=
p14617 (p14503 (Eq.refl true))
  (@p14359 3144099898276 35184372088832 8572435944177664
    p4996 786024974569 8796093022208 8175311989
    907097092915200000000 (p14553 (Eq.refl true))
    (Eq.refl true))

noncomputable def p14619 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 4 1) Real.pi)
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p14324 (Enclosure.sfrac false 1 16))))
  884279719003555

noncomputable def p14620 :=
@p14619 70368744177664 1 250000000000000 8760902761399
  8796093022208 8175311989 907097092915200000000 p14611
  p504 p14612 p12348

noncomputable def p14621 :=
p14620 d199
  (@p14505 35043611045596 35184372088832 8572435944177664
    p4996 8760902761399 8796093022208 8175311989
    907097092915200000000 (p14531 (Eq.refl true))
    (Eq.refl true))

noncomputable def p14622 :=
@p14606 p14593 p14589
  (@p14614 p14601 p14602
    (@p14615 true p14608 p14600 p14609
      p14610 (p14618 (Eq.refl true)))
    (p14621 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p14623 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1) p14404)
  (@iteratedDeriv Real c11 Real
    Real.normedAddCommGroup
    c8
    (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
      (Enclosure.sfrac false 12 1)))
  p14563

noncomputable def p14624 :=
nat_lit 368751084996723296685910334749900934363246427812156017783015727771975

noncomputable def p14625 :=
nat_lit 4596193466995848473550331679814519716475535784377624818301420034544148482758022877109

noncomputable def p14626 :=
nat_lit 2187444412747550512581495898199407592683348825286826747053998080000000000000000000000000000000

noncomputable def p14627 :=
@p14623 p12265 p14557 p12348
  p14624 p12388 p14625 p14626
  p14603 p14587 p14604 p14589

noncomputable def p14628 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 2 1) p14404
  2 1 0 1 p14563 p12189

noncomputable def p14629 :=
@Neg.neg Real Real.instNeg
  (p14398
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p14324 (Enclosure.sfrac false 1 16)))))

noncomputable def p14630 :=
@Enclosure.Real.IsNear.of_eq
  (@iteratedDeriv Real c11 Real
    Real.normedAddCommGroup
    c8
    (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
      (Enclosure.sfrac false 12 1)))
  (p14323
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14629
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p14404
        (Zeta.RiemannSiegel.correction
          (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
            (Enclosure.sfrac false 12 1))))))

noncomputable def p14631 :=
@p14327
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14629
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p14404
      (Zeta.RiemannSiegel.correction
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
          (Enclosure.sfrac false 12 1)))))
  371607888103645

noncomputable def p14632 :=
nat_lit 992312318445390713667083983512954964217676161238576755

noncomputable def p14633 :=
nat_lit 12268609770350041695778595258872258868238881064385575995152931653080481

noncomputable def p14634 :=
nat_lit 31085454747135806209449468414610004070416221470720000000000000000000000000000000

noncomputable def p14635 :=
@p14631 70368744177664 7369 70368744177664 p14632
  p2977 p14633 p14634 p14624
  p12388 p14625 p14626

noncomputable def p14636 :=
nat_lit 119758574419198491349395385110541166276215

noncomputable def p14637 :=
@Enclosure.Real.IsNear.subLit_ff_n p14629
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p14404
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
        (Enclosure.sfrac false 12 1))))
  p14636 p14032

noncomputable def p14638 :=
nat_lit 367516421296817070852204599768285372978581582547

noncomputable def p14639 :=
nat_lit 11423053088776620782767091924284211200000000000000000000000

noncomputable def p14640 :=
nat_lit 17846833291218020090795682336961084427080860939753500275

noncomputable def p14641 :=
nat_lit 11268490538279219707988076046423939312150056548896157442139888453080481

noncomputable def p14642 :=
nat_lit 43221297209011401685240432450415540760528883845934761287704895159061019710214200859817767075840

noncomputable def p14643 :=
@p14637 p14638 p14639 p14640
  p2977 p14641 p14634 p14642
  p14632 p2977 p14633 p14634

noncomputable def p14644 :=
@Enclosure.Real.IsNear.neg
  (p14398
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p14324 (Enclosure.sfrac false 1 16)))))

noncomputable def p14645 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p14646 :=
@p14645
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p14324 (Enclosure.sfrac false 1 16))))
  p14490

noncomputable def p14647 :=
@p14646 p12265 p14491 p14492
  8760902761399 8796093022208 8175311989 907097092915200000000
  p14636 p14032 p14638 p14639

noncomputable def p14648 :=
p14647
  (p14498 d197
    (p14500 (p14502 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (@p14505 35043611045596 35184372088832 8572435944177664
    p4996 8760902761399 8796093022208 8175311989
    907097092915200000000 (p14531 (Eq.refl true))
    (Eq.refl true))

noncomputable def p14649 :=
@Enclosure.Real.IsNear.mulLit_ff p14404
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
      (Enclosure.sfrac false 12 1)))
  p14563 p12189 p14557

noncomputable def p14650 :=
nat_lit 292093080796307358761204005

noncomputable def p14651 :=
nat_lit 1817666454004168085135923

noncomputable def p14652 :=
@p14327
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p14324 (Enclosure.sfrac false 1 16))))
  371607888103645

noncomputable def p14653 :=
@p14652 70368744177664 7369 70368744177664 786024974569
  8796093022208 8175311989 907097092915200000000 p14650
  p504 p14651 p14048

noncomputable def p14654 :=
p14653
  (p14416
    (@Enclosure.Real.IsNear.neg p14331 false 371607888103645 70368744177664
      7369 70368744177664 (p14445 (Eq.refl true))))
  (@p14359 3144099898276 35184372088832 8572435944177664
    p4996 786024974569 8796093022208 8175311989
    907097092915200000000 (p14553 (Eq.refl true))
    (Eq.refl true))

noncomputable def p14655 :=
@p14649 p13957 p14650 p504
  p14651 p14048 p14640 p2977
  p14641 p14634
  (@p14565 true p14563 p12189 p14557
    p13957 (p14580 (Eq.refl true)))
  (@p14325 false p14650 p504 p14651
    p14048
    (BSN.correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
        (Enclosure.sfrac false 12 1))
      (p14326 (Eq.refl true) (Eq.refl true)
        (p14102 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p14654 (Eq.refl true)))

noncomputable def p14656 :=
p14635
  (p14416
    (@Enclosure.Real.IsNear.neg p14331 false 371607888103645 70368744177664
      7369 70368744177664 (p14445 (Eq.refl true))))
  (p14643
    (@p14644 true p14636 p14032 p14638
      p14639 (p14648 (Eq.refl true)))
    (p14655 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p14657 :=
p14627
  (@p14628 p14557 p13957 p14563
    p12265 p14557 p12348
    (Enclosure.Real.IsNear.const false 2 1)
    (@p14565 true p14563 p12189 p14557
      p13957 (p14580 (Eq.refl true)))
    (Eq.refl true))
  (@p14630 false p14624 p12388 p14625
    p14626
    (BSN.deriv_correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
        (Enclosure.sfrac false 12 1))
      (p14326 (Eq.refl true) (Eq.refl true)
        (p14102 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p14656 (Eq.refl true)))

noncomputable def p14658 :=
nat_lit 5209835496042649738792207363889431025810575

noncomputable def p14659 :=
nat_lit 2480333553272904586630015773597965091913598337930900141418771

noncomputable def p14660 :=
@Enclosure.Real.IsNear.mulLit_ff p14406
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
      (Enclosure.sfrac false 12 1)))
  p14658 p12284 p14659

noncomputable def p14661 :=
@Enclosure.Real.IsNear.neg
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 4 1)
      c16)
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
          (Enclosure.sfrac false 12 1)))))

noncomputable def p14662 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 4 1)
    c16)
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
        (Enclosure.sfrac false 12 1))))
  p1068

noncomputable def p14663 :=
@p14662 p1070 p1071 p1072
  6662614432663 35184372088832 3405780739 907097092915200000000
  p14658 p12284 p14659 p14058

noncomputable def p14664 :=
p14663 d201
  (@p14335 13325228865326 70368744177664 3571219944177664
    p4996 6662614432663 35184372088832 3405780739
    907097092915200000000
    (p14429 (p14442 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p14665 :=
@p14660 p14058 p14650 p504
  p14651 p14048 p14594 p12388
  p14595 p13990
  (@p14661 true p14658 p12284 p14659
    p14058 (p14664 (Eq.refl true)))
  (@p14325 false p14650 p504 p14651
    p14048
    (BSN.correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
        (Enclosure.sfrac false 12 1))
      (p14326 (Eq.refl true) (Eq.refl true)
        (p14102 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p14654 (Eq.refl true)))

noncomputable def p14666 :=
p14590
  (p14416
    (@Enclosure.Real.IsNear.neg p14331 false 371607888103645 70368744177664
      7369 70368744177664 (p14445 (Eq.refl true))))
  (p14597
    (p14622 (p14657 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true))
    (p14665 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p14667 :=
p14562
  (@p14564 p14557 p13957 p14555
    p12189 p14557 p13950
    (Enclosure.Real.IsNear.const false 3 1)
    (@p14565 true p14563 p12189 p14557
      p13957 (p14580 (Eq.refl true)))
    (Eq.refl true))
  (@p14584 false p14558 p14559 p14560
    p14561
    (BSN.iteratedDeriv_two_correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
        (Enclosure.sfrac false 12 1))
      (p14326 (Eq.refl true) (Eq.refl true)
        (p14102 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p14666 (Eq.refl true)))

noncomputable def p14668 :=
@p14470 p14456 p14414
  (@p14480 p14465 p14466
    (p14532 (Eq.refl true)) (p14554 (Eq.refl true))
    (Eq.refl true) (Eq.refl true))
  (p14667 (Eq.refl true)) (Eq.refl true) (Eq.refl true)

noncomputable def p14669 :=
nat_lit 15629506488127949216376622091668293077431725

noncomputable def p14670 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 3 1) p14406)
  (@iteratedDeriv Real c11 Real
    Real.normedAddCommGroup
    c8
    (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
      (Enclosure.sfrac false 12 1)))
  p14669

noncomputable def p14671 :=
@p14670 p12284 p14659 p14069
  p14624 p12388 p14625 p14626
  p14457 p14458 p14459 p14460

noncomputable def p14672 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 3 1) p14406
  3 1 0 1 p14658 p12284

noncomputable def p14673 :=
p14671
  (@p14672 p14659 p14058 p14669
    p12284 p14659 p14069
    (Enclosure.Real.IsNear.const false 3 1)
    (@p14661 true p14658 p12284 p14659
      p14058 (p14664 (Eq.refl true)))
    (Eq.refl true))
  (@p14630 false p14624 p12388 p14625
    p14626
    (BSN.deriv_correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
        (Enclosure.sfrac false 12 1))
      (p14326 (Eq.refl true) (Eq.refl true)
        (p14102 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p14656 (Eq.refl true)))

noncomputable def p14674 :=
nat_lit 47777038554890657543493833803890630688866681498152489491375

noncomputable def p14675 :=
nat_lit 66949034574263296008558228404035713138915077920477999845854754715497507581150910479557

noncomputable def p14676 :=
@Enclosure.Real.IsNear.mulLit_tf p14408
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
      (Enclosure.sfrac false 12 1)))
  p14674 p14074 p14675

noncomputable def p14677 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 8 1)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      c16 Real.pi))
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
        (Enclosure.sfrac false 12 1))))

noncomputable def p14678 :=
@p14677 p1059 p1061 p1062
  p1063 69095574625501 70368744177664 3405780739
  907097092915200000000 p14674 p14074 p14675

noncomputable def p14679 :=
@p14678 p14077 d202
  (@p14568 69095574625501 70368744177664 3571219944177664
    p4996 69095574625501 70368744177664 3405780739
    907097092915200000000
    (p14570 (p14579 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p14680 :=
@p14676 p14077 p14650 p504
  p14651 p14048 p14449 p12222
  p14450 p14451 (p14679 (Eq.refl true))
  (@p14325 false p14650 p504 p14651
    p14048
    (BSN.correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
        (Enclosure.sfrac false 12 1))
      (p14326 (Eq.refl true) (Eq.refl true)
        (p14102 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p14654 (Eq.refl true)))

noncomputable def p14681 :=
p14415
  (p14416
    (@Enclosure.Real.IsNear.neg p14331 false 371607888103645 70368744177664
      7369 70368744177664 (p14445 (Eq.refl true))))
  (p14453
    (@p14462 p14448 p14414 p14668
      (p14673 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true))
    (p14680 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p14682 :=
@p14397 p14390
  (@p14409 false p14394 p2658 p14395
    p14396
    (BSN.iteratedDeriv_three_correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
        (Enclosure.sfrac false 12 1))
      (p14326 (Eq.refl true) (Eq.refl true)
        (p14102 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p14681 (Eq.refl true)))

noncomputable def p14683 :=
@p14388 p14389 p14390 1350652745 17179869184
  1 17179869184 p14318 p14295 p14319
  p14320
  (@p14392 p14387 p14389 p14390
    (BSN.correctionLinear_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p14099
        (Enclosure.sfrac false 12 1)))
    (@Enclosure.Real.IsNear.neg p14391 false p14386 p14387
      p14389 p14390
      (p14682 d203 (Eq.refl true))))

noncomputable def p14684 :=
@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv p14099) false
  1350652745 17179869184 1 17179869184 1350652745
  17179869184

noncomputable def p14685 :=
@Enclosure.Real.IsNear.inv_image p14099 218522419133 17179869184 41
  17179869184 675326372 675326373 8589934592
  (p14313 (Eq.refl true)) (Eq.refl true) (Eq.refl true)

noncomputable def p14686 :=
p14385
  (p14683
    (@p14684 1 17179869184
      (p14685 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (Eq.refl true))
    (Eq.refl true))

noncomputable def p14687 :=
@p14298 p14094
  (@p14300 8589934592
    (@p2563 1 0 1
      (BSN.neg_one_pow_even_mk 12 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1))
    p14316 (Eq.refl true))
  (p14686 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p14688 :=
@p14101 p14091 p14093 p14094
  (BSN.hardyZApproximantRS_eq
    (@OfScientific.ofScientific Real c2 101655800
      true 5)
    12
    (p14102 (Eq.refl true) (Eq.refl true)
      (Eq.refl true)))
  (p14292 p14687 (Eq.refl true) (Eq.refl true))

theorem d215 : p14092 p14093 p14094 :=
@p14095 p14091 p14093 p14094
  (@Eq.refl Real
    (hardyZApproximantRS
      (@OfScientific.ofScientific Real c2 101655800
        true 5)))
  p14688

noncomputable def p14689 :=
Enclosure.Real.IsNear
  (hardyZErrorBoundRS
    (@OfScientific.ofScientific Real c2 101532600
      true 5))
  false 5963727889 549755813888

noncomputable def p14690 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Real.sqrt p13493)
  (@HDiv.hDiv Real Real Real c4
    (@OfScientific.ofScientific Real c2 101532600
      true 5)
    c7)

noncomputable def p14691 :=
@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 25 4) (@Inv.inv Real Real.instInv p14690))
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 1 32)
    (@Inv.inv Real Real.instInv
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p14690
          p14690)
        p14690)))

noncomputable def p14692 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZErrorBoundRS
    (@OfScientific.ofScientific Real c2 101532600
      true 5))
  p14691 false 5963727889

noncomputable def p14693 :=
BSN.hardyZErrorBoundRS_mk
  (@OfScientific.ofScientific Real c2 101532600
    true 5)
  101532600 100000
  (Enclosure.sfrac_ofScientific_eq 101532600 5 100000 (Eq.refl true))
  (Eq.refl true)

noncomputable def p14694 :=
@Enclosure.Real.IsNear.addLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 25 4) (@Inv.inv Real Real.instInv p14690))
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 1 32)
    (@Inv.inv Real Real.instInv
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p14690
          p14690)
        p14690)))

noncomputable def p14695 :=
@p14694 745465975 68719476736 25 68719476736 89
  549755813888 1 549755813888 409824259927969890304 5963727889
  549755813888

noncomputable def p14696 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 25 4)
  (@Inv.inv Real Real.instInv p14690) 25 4 0 1
  29818639 17179869184

noncomputable def p14697 :=
@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv p14690) false 29818639
  17179869184 1 17179869184 29818639 17179869184

noncomputable def p14698 :=
nat_lit 85024044220680879571602891

noncomputable def p14699 :=
@Enclosure.Real.IsNear.mulLit_ff (Real.sqrt p13493)
  (@HDiv.hDiv Real Real Real c4
    (@OfScientific.ofScientific Real c2 101532600
      true 5)
    c7)

noncomputable def p14700 :=
@p14699 61252844619 17179869184 7 17179869184
  1388083194332289 8589934592000 507663 8589934592000 p14698
  147573952589676412928000 40812385221695061

noncomputable def p14701 :=
@p14700 147573952589676412928000
  (p13698
    (p13707 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (p13702 (p13704 (Eq.refl true))) (Eq.refl true)

noncomputable def p14702 :=
@Enclosure.Real.IsNear.inv_image p14690 p14698 147573952589676412928000
  40812385221695061 147573952589676412928000 14909319 14909320
  8589934592 p14701 (Eq.refl true) (Eq.refl true)

noncomputable def p14703 :=
@p14695 201 549755813888
  (@p14696 1 17179869184 745465975 68719476736 25
    68719476736 (Enclosure.Real.IsNear.const false 25 4)
    (@p14697 1 17179869184
      (p14702 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (Eq.refl true))
    (Eq.refl true))

noncomputable def p14704 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 1 32)
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p14690
        p14690)
      p14690))
  1

noncomputable def p14705 :=
@p14704 32 0 1 89 17179869184 1
  17179869184 89 549755813888 1 549755813888

noncomputable def p14706 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p14690
        p14690)
      p14690))
  false

noncomputable def p14707 :=
nat_lit 614646305918918397394672083787955568386445716990020580828723781159195501433971

noncomputable def p14708 :=
@Enclosure.Real.IsNear.inv_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p14690
      p14690)
    p14690)
  p14707 p3667

noncomputable def p14709 :=
nat_lit 885108984907386428762365938103024750889401006925377837603427998231437

noncomputable def p14710 :=
nat_lit 7229088095640297678009381318318706176372242999557881

noncomputable def p14711 :=
nat_lit 6940068093347378165854908038940053647836423

noncomputable def p14712 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p14690
    p14690)
  p14690 p14710 p3671 p14711

noncomputable def p14713 :=
@Enclosure.Real.IsNear.mulLit_ff p14690 p14690 p14698
  147573952589676412928000 40812385221695061 147573952589676412928000
  p14698 147573952589676412928000 40812385221695061
  147573952589676412928000 p14710

noncomputable def p14714 :=
@p14712 p3671 p14698 147573952589676412928000
  40812385221695061 147573952589676412928000 p14707 p3667
  p14709 p3667
  (@p14713 p3671 p14711 p3671
    p14701 p14701 (Eq.refl true))
  p14701

noncomputable def p14715 :=
@p14708 p14709 p3667 44 45
  8589934592 (p14714 (Eq.refl true)) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p14716 :=
p14705 (Enclosure.Real.IsNear.const false 1 32)
  (@p14706 89 17179869184 1 17179869184 89
    17179869184 1 17179869184 (p14715 (Eq.refl true))
    (Eq.refl true))

theorem d216 : p14689 201 549755813888 :=
@p14692 549755813888 201 549755813888
  (p14693 (Eq.refl true))
  (p14703 (p14716 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p14717 :=
Enclosure.Real.IsNear
  (hardyZErrorBoundRS
    (@OfScientific.ofScientific Real c2 101655800
      true 5))
  false 5954694689 549755813888

noncomputable def p14718 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Real.sqrt p14099)
  (@HDiv.hDiv Real Real Real c4
    (@OfScientific.ofScientific Real c2 101655800
      true 5)
    c7)

noncomputable def p14719 :=
@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 25 4) (@Inv.inv Real Real.instInv p14718))
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 1 32)
    (@Inv.inv Real Real.instInv
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p14718
          p14718)
        p14718)))

noncomputable def p14720 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZErrorBoundRS
    (@OfScientific.ofScientific Real c2 101655800
      true 5))
  p14719 false 5954694689

noncomputable def p14721 :=
BSN.hardyZErrorBoundRS_mk
  (@OfScientific.ofScientific Real c2 101655800
    true 5)
  101655800 100000
  (Enclosure.sfrac_ofScientific_eq 101655800 5 100000 (Eq.refl true))
  (Eq.refl true)

noncomputable def p14722 :=
@Enclosure.Real.IsNear.addLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 25 4) (@Inv.inv Real Real.instInv p14718))
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 1 32)
    (@Inv.inv Real Real.instInv
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p14718
          p14718)
        p14718)))

noncomputable def p14723 :=
@p14722 744336825 68719476736 25 68719476736 89
  549755813888 1 549755813888 409203503150718255104 5954694689
  549755813888

noncomputable def p14724 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 25 4)
  (@Inv.inv Real Real.instInv p14718) 25 4 0 1
  29773473 17179869184

noncomputable def p14725 :=
@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv p14718) false 29773473
  17179869184 1 17179869184 29773473 17179869184

noncomputable def p14726 :=
nat_lit 85153024351425644616869727

noncomputable def p14727 :=
@Enclosure.Real.IsNear.mulLit_ff (Real.sqrt p14099)
  (@HDiv.hDiv Real Real Real c4
    (@OfScientific.ofScientific Real c2 101655800
      true 5)
    c7)

noncomputable def p14728 :=
@p14727 61271417271 17179869184 7 17179869184
  1389767499171737 8589934592000 508279 8589934592000 p14726
  147573952589676412928000 40871347196846721

noncomputable def p14729 :=
@p14728 147573952589676412928000
  (p14305
    (p14314 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (p14309 (p14311 (Eq.refl true))) (Eq.refl true)

noncomputable def p14730 :=
@Enclosure.Real.IsNear.inv_image p14718 p14726 147573952589676412928000
  40871347196846721 147573952589676412928000 14886736 14886737
  8589934592 p14729 (Eq.refl true) (Eq.refl true)

noncomputable def p14731 :=
@p14723 201 549755813888
  (@p14724 1 17179869184 744336825 68719476736 25
    68719476736 (Enclosure.Real.IsNear.const false 25 4)
    (@p14725 1 17179869184
      (p14730 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (Eq.refl true))
    (Eq.refl true))

noncomputable def p14732 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 1 32)
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p14718
        p14718)
      p14718))
  1

noncomputable def p14733 :=
@p14732 32 0 1 89 17179869184 1
  17179869184 89 549755813888 1 549755813888

noncomputable def p14734 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p14718
        p14718)
      p14718))
  false

noncomputable def p14735 :=
nat_lit 617447777595731202828972632614483916088309418593798138151123531745090992343583

noncomputable def p14736 :=
@Enclosure.Real.IsNear.inv_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p14718
      p14718)
    p14718)
  p14735 p3667

noncomputable def p14737 :=
nat_lit 889079020916535713996224210110534763367280966097583695894858929763809

noncomputable def p14738 :=
nat_lit 7251037556194488824051541030591314530686636089054529

noncomputable def p14739 :=
nat_lit 278425505917111568279091971466550306267287

noncomputable def p14740 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p14718
    p14718)
  p14718 p14738 p3671 p14739

noncomputable def p14741 :=
nat_lit 871122859317602466466238995025326621327360000

noncomputable def p14742 :=
@Enclosure.Real.IsNear.mulLit_ff p14718 p14718 p14726
  147573952589676412928000 40871347196846721 147573952589676412928000
  p14726 147573952589676412928000 40871347196846721
  147573952589676412928000 p14738

noncomputable def p14743 :=
@p14740 p14741 p14726 147573952589676412928000
  40871347196846721 147573952589676412928000 p14735 p3667
  p14737 p3667
  (@p14742 p3671 p14739 p14741
    p14729 p14729 (Eq.refl true))
  p14729

noncomputable def p14744 :=
@p14736 p14737 p3667 44 45
  8589934592 (p14743 (Eq.refl true)) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p14745 :=
p14733 (Enclosure.Real.IsNear.const false 1 32)
  (@p14734 89 17179869184 1 17179869184 89
    17179869184 1 17179869184 (p14744 (Eq.refl true))
    (Eq.refl true))

theorem d217 : p14717 201 549755813888 :=
@p14720 549755813888 201 549755813888
  (p14721 (Eq.refl true))
  (p14731 (p14745 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p14746 :=
@LE.le Real Real.instLE
  c18
  (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE d36))

noncomputable def p14747 :=
@OfNat.ofNat Real 507663
  (@instOfNatAtLeastTwo Real 507663
    (@AddMonoidWithOne.toNatCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real
            (@DivisionSemiring.toSemiring Real
              c3)))))
    (Mathlib.Meta.NormNum.instAtLeastTwo 507661))

noncomputable def p14748 :=
@LE.le Real Real.instLE
  c18
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            c3))))
    p14747 p4068)

noncomputable def p14749 :=
@congrArg Real Prop (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE d36))
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            c3))))
    p14747 p4068)

noncomputable def p14750 :=
p14749
  (@LE.le Real Real.instLE
    c17)

noncomputable def p14751 :=
@Mathlib.Meta.NormNum.IsNNRat.to_eq Real
  c3 507663 500
  (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE d36)) p14747
  p4068
  (@Mathlib.Meta.NormNum.isNNRat_ofScientific_of_true Real
    c3 101532600
    5 507663 500
    (p219
      (p220 p4
        (@p221 507663 500
          (p225 (@Eq.refl Nat (Nat.mul 101532600 1))
            (@Eq.refl Nat 100000))))))
  (@Eq.refl Real p14747)

noncomputable def p14752 :=
@congrArg Real Prop
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            c3))))
    p14747 p4068)

noncomputable def p14753 :=
@p14752
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            c3))))
    p14747 p4068)

noncomputable def p14754 :=
p14753
  (@LE.le Real Real.instLE
    c17)

noncomputable def p14755 :=
@Mathlib.Meta.NormNum.IsNNRat.to_eq Real
  c3 507663 500
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            c3))))
    p14747 p4068)

noncomputable def p14756 :=
@Mathlib.Meta.NormNum.isNNRat_mul Real
  (@DivisionSemiring.toSemiring Real
    c3)
  (@HMul.hMul Real Real Real
    c19)
  p14747
  (@Inv.inv Real
    (@InvOneClass.toInv Real
      (@DivInvOneMonoid.toInvOneClass Real
        (@DivisionMonoid.toDivInvOneMonoid Real
          (@GroupWithZero.toDivisionMonoid Real
            (@DivisionSemiring.toGroupWithZero Real
              c3)))))
    p4068)

noncomputable def p14757 :=
@p14756 507663 1 507663 1 500 500
  1
  (@Eq.refl (Real → Real → Real)
    (@HMul.hMul Real Real Real
      c19))
  (@Mathlib.Meta.NormNum.IsNat.to_isNNRat Real
    (@DivisionSemiring.toSemiring Real
      c3)
    p14747 507663
    (@Mathlib.Meta.NormNum.isNat_ofNat Real
      c5
      p14747 507663
      (@Eq.refl Real
        (@OfNat.ofNat Real 507663
          (@instOfNatAtLeastTwo Real 507663
            (@AddMonoidWithOne.toNatCast Real
              c5)
            (Mathlib.Meta.NormNum.instAtLeastTwo 507661))))))

noncomputable def p14758 :=
@p14755 p14747 p4068
  (@Mathlib.Meta.NormNum.isNNRat_div Real
    c3 p14747
    p4068 507663 500
    (p14757 p4091 (@Eq.refl Nat (Nat.mul 507663 1))
      (@Eq.refl Nat 500)))
  (@Eq.refl Real p14747)

noncomputable def p14759 :=
@le_of_not_gt Real Real.linearOrder
  c18
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            c3))))
    p14747 p4068)

noncomputable def p14760 :=
@LT.lt Real
  (@Preorder.toLT Real (@PartialOrder.toPreorder Real (@LinearOrder.toPartialOrder Real Real.linearOrder)))
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            c3))))
    p14747 p4068)

noncomputable def p14761 :=
@HMul.hMul Real Real Real
  c19
  c14

noncomputable def p14762 :=
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
  p14747

noncomputable def p14763 :=
@HSub.hSub Real Real Real
  (@instHSub Real
    (@SubNegMonoid.toSub Real
      (@AddGroup.toSubNegMonoid Real
        (@AddGroupWithOne.toAddGroup Real
          (@Ring.toAddGroupWithOne Real
            c32)))))
  p14762
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real
          (@DivisionSemiring.toSemiring Real
            c3))))
    p3705 (p8250 Real.pi))

noncomputable def p14764 :=
@HAdd.hAdd Real Real Real
  c36
  (p14761
    c13)
  p14763

noncomputable def p14765 :=
@Eq.mp
  (@LT.lt Real c29
    (@HAdd.hAdd Real Real Real
      c36
      p14764 (p8253 p3713))
    (@OfNat.ofNat Real 0
      c48))
  (@LT.lt Real c29
    c25
    (@OfNat.ofNat Real 0
      c48))

noncomputable def p14766 :=
@Mathlib.Tactic.Ring.Common.add_congr Real Real.instCommSemiring p14764
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@Mathlib.Meta.NormNum.instAddMonoidWithOne Real
        (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing)))
      50400)
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))
      p8255
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))))
  (p8253 p3713)

noncomputable def p14767 :=
@p14766
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 50400))
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))
      p8257
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))))
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))

noncomputable def p14768 :=
@Mathlib.Tactic.Ring.Common.add_congr Real Real.instCommSemiring
  (p14761
    c13)
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 457263))
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))

noncomputable def p14769 :=
@p14768 p14763
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      507663)
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))
      p8255
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
      50400)
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))
      p8255
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))))

noncomputable def p14770 :=
@Mathlib.Tactic.Ring.Common.mul_congr Real Real.instCommSemiring
  c14

noncomputable def p14771 :=
@p14770
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      457263)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@Neg.neg Real
    c37
    c23)

noncomputable def p14772 :=
@Mathlib.Tactic.Ring.cast_pos Real Real.instCommSemiring
  c14

noncomputable def p14773 :=
@Mathlib.Meta.NormNum.isNat_ofNat Real
  c5
  c14

noncomputable def p14774 :=
@p14771
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
      (Int.negOfNat 457263))
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@p14772 457263
    (@p14773 457263
      (@Eq.refl Real
        (@OfNat.ofNat Real 457263
          (@instOfNatAtLeastTwo Real 457263
            (@AddMonoidWithOne.toNatCast Real
              c5)
            (Mathlib.Meta.NormNum.instAtLeastTwo 457261))))))

noncomputable def p14775 :=
@Mathlib.Tactic.Ring.Common.add_mul Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    457263)
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
      (Int.negOfNat 457263))
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))

noncomputable def p14776 :=
@Mathlib.Tactic.Ring.Common.mul_add Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    457263)
  (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (Int.negOfNat 1))
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (Int.negOfNat 457263))

noncomputable def p14777 :=
@Mathlib.Meta.NormNum.IsInt.to_raw_eq Real
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      457263)
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 1)))
  (Int.negOfNat 457263)

noncomputable def p14778 :=
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
    457263)
  (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (Int.negOfNat 1))

noncomputable def p14779 :=
@p14778 (Int.ofNat 457263) (Int.negOfNat 1) (Int.negOfNat 457263)
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
      457263)
    457263
    (@Mathlib.Meta.NormNum.IsNat.of_raw Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      457263))

noncomputable def p14780 :=
@p14776
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 457263))
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@p14777 (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (p14779
      (@Mathlib.Meta.NormNum.IsInt.of_raw Real
        (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing)) (Int.negOfNat 1))
      (@Eq.refl Int (Int.negOfNat 457263))))
  (@Mathlib.Tactic.Ring.Common.mul_zero Real Real.instCommSemiring
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      457263))

noncomputable def p14781 :=
@p14775
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 457263))
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (p14780
    (@Mathlib.Tactic.Ring.Common.add_pf_add_zero Real Real.instCommSemiring
      (@HAdd.hAdd Real Real Real
        (@instHAdd Real
          (@Distrib.toAdd Real
            (@instDistribOfSemiring Real c0)))
        (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
          (Int.negOfNat 457263))
        (@OfNat.ofNat Real 0
          (@Zero.toOfNat0 Real
            (@MulZeroClass.toZero Real
              (@instMulZeroClassOfSemiring Real c0)))))))

noncomputable def p14782 :=
p14781
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
        (Int.negOfNat 457263))
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))))

noncomputable def p14783 :=
p14769
  (p14774
    (p3726 p3727
      (p3728
        (@Mathlib.Meta.NormNum.IsInt.to_raw_eq Real p3729 (Int.negOfNat 1)
          (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
          (p3733 (@Eq.refl Int (Int.negOfNat 1))))
        c65))
    p14782)

noncomputable def p14784 :=
@Mathlib.Tactic.Ring.Common.sub_congr Real Real.commRing p14762
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      507663)
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
    p3705 (p8250 Real.pi))

noncomputable def p14785 :=
@p3744 p14747
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      507663)
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
      507663)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))

noncomputable def p14786 :=
p14785
  (p3746
    (p3747
      (@Nat.cast_one Real
        c5)))
  (@Mathlib.Tactic.Ring.cast_pos Real Real.instCommSemiring p14747 507663
    (@Mathlib.Meta.NormNum.isNat_ofNat Real
      c5
      p14747 507663
      (@Eq.refl Real
        (@OfNat.ofNat Real 507663
          (@instOfNatAtLeastTwo Real 507663
            (@AddMonoidWithOne.toNatCast Real
              c5)
            (Mathlib.Meta.NormNum.instAtLeastTwo 507661))))))

noncomputable def p14787 :=
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
      507663)
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
      507663)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))

noncomputable def p14788 :=
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
    507663)
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    507663)

noncomputable def p14789 :=
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
      507663))
  507663

noncomputable def p14790 :=
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
    507663)
  1 507663

noncomputable def p14791 :=
@p14790 507663
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
    507663)
  (@Eq.refl Nat 507663)

noncomputable def p14792 :=
@p14788
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
      507663)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@p14789
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    p14791)

noncomputable def p14793 :=
p14792
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
        507663)
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))))

noncomputable def p14794 :=
@p14787
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
      507663)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  p14793

noncomputable def p14795 :=
p14794
  (@Mathlib.Tactic.Ring.Common.zero_mul Real Real.instCommSemiring
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))
      (@Nat.rawCast Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne Real
          (@NonAssocSemiring.toAddCommMonoidWithOne Real
            (@Semiring.toNonAssocSemiring Real c0)))
        507663)
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))))

noncomputable def p14796 :=
p14795
  (@Mathlib.Tactic.Ring.Common.add_pf_add_zero Real Real.instCommSemiring
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))
      (@Nat.rawCast Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne Real
          (@NonAssocSemiring.toAddCommMonoidWithOne Real
            (@Semiring.toNonAssocSemiring Real c0)))
        507663)
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))))

noncomputable def p14797 :=
@p14784
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p8257
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
      507663)
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))
      p8255
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))))
  (p14786 p14796)

noncomputable def p14798 :=
@Mathlib.Tactic.Ring.Common.sub_pf Real Real.commRing
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      507663)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p8257
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))

noncomputable def p14799 :=
@p14798
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p8255
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
      507663)
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))
      p8255
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))))
  p8321

noncomputable def p14800 :=
@Mathlib.Tactic.Ring.Common.add_pf_add_lt Real Real.instCommSemiring
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p8255
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p8255
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    507663)

noncomputable def p14801 :=
p14799
  (p14800
    (@Mathlib.Tactic.Ring.Common.add_pf_zero_add Real Real.instCommSemiring
      (@HAdd.hAdd Real Real Real
        (@instHAdd Real
          (@Distrib.toAdd Real
            (@instDistribOfSemiring Real c0)))
        p8255
        (@OfNat.ofNat Real 0
          (@Zero.toOfNat0 Real
            (@MulZeroClass.toZero Real
              (@instMulZeroClassOfSemiring Real c0)))))))

noncomputable def p14802 :=
@Mathlib.Tactic.Ring.Common.add_pf_add_overlap Real Real.instCommSemiring
  (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (Int.negOfNat 457263))
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    507663)
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p8255
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@Nat.rawCast Real
    (@Mathlib.Meta.NormNum.instAddMonoidWithOne Real
      (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing)))
    50400)
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p8255
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))

noncomputable def p14803 :=
@Mathlib.Meta.NormNum.IsNat.to_raw_eq Real
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 457263))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      507663))
  50400
  (@Mathlib.Meta.NormNum.instAddMonoidWithOne Real
    (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing)))

noncomputable def p14804 :=
@Mathlib.Meta.NormNum.isInt_add Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0))))
  (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (Int.negOfNat 457263))
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    507663)
  (Int.negOfNat 457263) (Int.ofNat 507663)

noncomputable def p14805 :=
@p14804 (Int.ofNat 50400)
  (@Eq.refl (Real → Real → Real)
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))))
  (@Mathlib.Meta.NormNum.IsInt.of_raw Real
    (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing)) (Int.negOfNat 457263))
  (@Mathlib.Meta.NormNum.IsNat.to_isInt Real
    (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      507663)
    507663
    (@Mathlib.Meta.NormNum.IsNat.of_raw Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      507663))

noncomputable def p14806 :=
@Mathlib.Meta.NormNum.IsInt.to_isNat Real
  (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 457263))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      507663))
  50400 (p14805 (@Eq.refl Int (Int.ofNat 50400)))

noncomputable def p14807 :=
p14783
  (p14797
    (p8291 (p8297 p8306) p8315)
    p14801)
  (p14802 (p14803 p14806)
    (@Mathlib.Tactic.Ring.Common.add_pf_zero_add Real Real.instCommSemiring
      (@HAdd.hAdd Real Real Real
        (@instHAdd Real
          (@Distrib.toAdd Real
            (@instDistribOfSemiring Real c0)))
        p8255
        (@OfNat.ofNat Real 0
          (@Zero.toOfNat0 Real
            (@MulZeroClass.toZero Real
              (@instMulZeroClassOfSemiring Real c0)))))))

noncomputable def p14808 :=
@Mathlib.Tactic.Ring.of_eq Real
  (@HAdd.hAdd Real Real Real
    c36
    p14764 (p8253 p3713))
  c25
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (p14767 p14807
    (p8336
      (p3840 (p3842 p3852) p3860)
      p8354)
    (@p8355
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))
      p8358
      (p8363
        (@Mathlib.Tactic.Ring.Common.add_pf_zero_add Real Real.instCommSemiring
          (@OfNat.ofNat Real 0
            (@Zero.toOfNat0 Real
              (@MulZeroClass.toZero Real
                (@instMulZeroClassOfSemiring Real c0))))))))

noncomputable def p14809 :=
@congrArg Real Prop
  (@HAdd.hAdd Real Real Real
    c36
    p14764 (p8253 p3713))
  c25
  (fun (_a : Real) =>
    @LT.lt Real c29 _a
      (@OfNat.ofNat Real 0
        c48))
  (p14808
    (@Mathlib.Tactic.Ring.cast_zero Real Real.instCommSemiring
      c25
      (@Mathlib.Meta.NormNum.isNat_ofNat Real
        c5
        c25 0
        (@Nat.cast_zero Real
          c5))))

noncomputable def p14810 :=
@HAdd.hAdd Real Real Real
  (@instHAdd Real (@Distrib.toAdd Real (@instDistribOfSemiring Real Real.semiring)))
  (@HMul.hMul Real Real Real
    (@instHMul Real
      c50)
    c30
    c13)
  p14763

noncomputable def p14811 :=
@Mathlib.Tactic.Linarith.add_neg Real Real.semiring Real.partialOrder Real.instIsStrictOrderedRing
  (@HMul.hMul Real Real Real
    (@instHMul Real
      c50)
    c30
    c13)
  p14763

noncomputable def p14812 :=
@Mathlib.Tactic.Linarith.mul_neg Real Real.instRing Real.partialOrder Real.instIsStrictOrderedRing
  (@Neg.neg Real
    c37
    c23)
  c41
  (@neg_neg_of_pos Real Real.instAddCommGroup Real.partialOrder Real.instIsOrderedAddMonoid
    c23
    (@Mathlib.Tactic.Linarith.zero_lt_one Real Real.semiring Real.partialOrder Real.instIsStrictOrderedRing))

noncomputable def p14813 :=
@Mathlib.Meta.NormNum.isNat_lt_true Real Real.semiring Real.partialOrder Real.instIsOrderedRing
  (@FloorSemiring.instCharZero Real (@Ring.toSemiring Real Real.instRing) Real.partialOrder
    c26)
  c25
  c41
  0 457263
  (@Mathlib.Meta.NormNum.isNat_ofNat Real
    c5
    c25 0
    (@Nat.cast_zero Real
      c5))

noncomputable def p14814 :=
p14813
  (@Mathlib.Meta.NormNum.isNat_ofNat Real
    c5
    c30
    457263
    (@Eq.refl Real
      (@OfNat.ofNat Real 457263
        (@instOfNatAtLeastTwo Real 457263
          (@AddMonoidWithOne.toNatCast Real
            c5)
          (Mathlib.Meta.NormNum.instAtLeastTwo 457261)))))

noncomputable def p14815 :=
@HSub.hSub Real Real Real
  c51
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            c3))))
    p14747 p4068)

noncomputable def p14816 :=
p8371
  (p14815
    c17)

noncomputable def p14817 :=
@Mathlib.Tactic.CancelDenoms.derive_trans Real Real.instMul
  (p14815
    c17)

noncomputable def p14818 :=
@p14817
  (p14815
    c17)

noncomputable def p14819 :=
@p14818
  (@OfNat.ofNat Real 500
    (@instOfNatAtLeastTwo Real 500
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p14820 :=
@congrArg Real (Real → Real)
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            c3))))
    p14747 p4068)

noncomputable def p14821 :=
@p14820
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            c3))))
    p14747 p4068)

noncomputable def p14822 :=
@congrFun' Real Real p14815 p14815
  (p14821
    (@HSub.hSub Real Real Real
      c24)
    (p14758 (@Eq.refl Real p4068)))
  c18

noncomputable def p14823 :=
@p8380
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            c3))))
    p14747 p4068)

noncomputable def p14824 :=
@p14823
  c18
  p14762

noncomputable def p14825 :=
@p14824
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real
          (@DivisionSemiring.toSemiring Real
            c3))))
    p3705 (p8250 Real.pi))

noncomputable def p14826 :=
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
  p14747

noncomputable def p14827 :=
@p8385 p14747 p4068 p14762
  (@rfl Real p14826)
  (p8388 p8397
    (p3747
      (@Nat.cast_one Real
        c5)))
  (@p8399 500 p8401
    (@p8295 500
      (@Eq.refl Real
        (@OfNat.ofNat Real 500
          (@instOfNatAtLeastTwo Real 500
            (@AddMonoidWithOne.toNatCast Real
              c5)
            (Mathlib.Meta.NormNum.instAtLeastTwo 498))))))

noncomputable def p14828 :=
@Eq.mp
  (@LT.lt Real c29
    p14816
    c31)
  (@LT.lt Real c29
    p14763
    c31)
  (@congrArg Real Prop p14816 p14763
    (fun (_a : Real) =>
      @LT.lt Real c29 _a
        c49)
    (@p14819 p14763 p14822
      (p14825 p14827 p8407)))

noncomputable def p14829 :=
@Mathlib.Tactic.Linarith.mul_neg Real Real.instRing Real.partialOrder Real.instIsStrictOrderedRing
  (p14815
    c17)

noncomputable def p14830 :=
@Mathlib.Tactic.Linarith.sub_neg_of_lt Real Real.instRing Real.partialOrder Real.instIsOrderedRing
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            c3))))
    p14747 p4068)

noncomputable def p14831 :=
fun
    (a :
      p14760
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (@OfNat.ofNat Real 32
            (@instOfNatAtLeastTwo Real 32 Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 31 (instOfNatNat 31))
                c64)))
          Real.pi)) =>
  @Mathlib.Tactic.Linarith.lt_irrefl Real Real.instPreorder
    c25
    (p14765 p14809
      (@Mathlib.Tactic.Linarith.add_neg Real Real.semiring Real.partialOrder Real.instIsStrictOrderedRing
        p14810
        (@HMul.hMul Real Real Real
          (@instHMul Real
            c50)
          c39
          p3713)
        (p14811 (p14812 (p14814 (@Eq.refl Bool false)))
          (p14828
            (@p14829
              (@OfNat.ofNat Real 500
                (@instOfNatAtLeastTwo Real 500 Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 499 (instOfNatNat 499))
                    c63)))
              (@p14830
                (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                  (@OfNat.ofNat Real 32
                    (@instOfNatAtLeastTwo Real 32 Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 31 (instOfNatNat 31))
                        c64)))
                  Real.pi)
                a)
              (p8412 (@Eq.refl Bool false)))))
        (@Mathlib.Tactic.Linarith.mul_neg Real Real.instRing Real.partialOrder Real.instIsStrictOrderedRing
          p3713
          c39
          p3995 (p8414 (@Eq.refl Bool false)))))

noncomputable def p14832 :=
@Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal d36)
  (hardyZApproximantRS
    (@OfScientific.ofScientific Real c2 101532600
      true 5))
  false p13484 p13485

noncomputable def p14833 :=
@Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.fstVal d36) p13484
  p13485 p13487 p13488
  (@p14832 p13487 p13488
    (@Eq.refl Real
      (hardyZApproximantRS
        (@OfScientific.ofScientific Real c2 101532600
          true 5)))
    d214)

noncomputable def p14834 :=
@Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal d36)
  (hardyZApproximantRS
    (@OfScientific.ofScientific Real c2 101655800
      true 5))
  true p14090 p14091

noncomputable def p14835 :=
@Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.sndVal d36) p14090
  p14091 p14093 p14094
  (@p14834 p14093 p14094
    (@Eq.refl Real
      (hardyZApproximantRS
        (@OfScientific.ofScientific Real c2 101655800
          true 5)))
    d215)

noncomputable def p14836 :=
@Zeta.Certificates.ZIntervalRS.Certificate.mk d36
  (@Eq.mpr p14746 p14748
    (@id (@Eq Prop p14746 p14748)
      (@Eq.trans Prop p14746 p14748 p14748
        (p14750 (p14751 (@Eq.refl Real p4068)))
        (p14754 (p14758 (@Eq.refl Real p4068)))))
    (p14759 p14831))
  (BSN.mul_neg_of_pos_neg_r (Zeta.Certificates.ZIntervalRS.fstVal d36)
    (Zeta.Certificates.ZIntervalRS.sndVal d36)
    (p14833 (Eq.refl true) (Eq.refl true) (Eq.refl true))
    (p14835 (Eq.refl true) (Eq.refl true)
      (Eq.refl true)))

noncomputable def p14837 :=
@Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal d36)
  (hardyZErrorBoundRS (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE d36)))
  false false p13484 p13485 p13487

noncomputable def p14838 :=
@p14837 p13488 5963727889 549755813888 201
  549755813888
  (@p14832 p13487 p13488
    (@Eq.refl Real
      (hardyZApproximantRS
        (@OfScientific.ofScientific Real c2 101532600
          true 5)))
    d214)

noncomputable def p14839 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZErrorBoundRS (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE d36)))
  (hardyZErrorBoundRS
    (@OfScientific.ofScientific Real c2 101532600
      true 5))
  false 5963727889 549755813888

noncomputable def p14840 :=
p14838
  (@p14839 201 549755813888
    (@Eq.refl Real
      (hardyZErrorBoundRS
        (@OfScientific.ofScientific Real c2 101532600
          true 5)))
    d216)

noncomputable def p14841 :=
@Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal d36)
  (hardyZErrorBoundRS (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE d36)))
  true false p14090 p14091 p14093

noncomputable def p14842 :=
@p14841 p14094 5954694689 549755813888 201
  549755813888
  (@p14834 p14093 p14094
    (@Eq.refl Real
      (hardyZApproximantRS
        (@OfScientific.ofScientific Real c2 101655800
          true 5)))
    d215)

noncomputable def p14843 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZErrorBoundRS (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE d36)))
  (hardyZErrorBoundRS
    (@OfScientific.ofScientific Real c2 101655800
      true 5))
  false 5954694689 549755813888

noncomputable def p14844 :=
p14842
  (@p14843 201 549755813888
    (@Eq.refl Real
      (hardyZErrorBoundRS
        (@OfScientific.ofScientific Real c2 101655800
          true 5)))
    d217)

theorem d218 : Zeta.Certificates.ZIntervalRS.Certificate d36 :=
p14836
  (p14840 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (p14844 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
end RHHeight1000.GramZero660

theorem solution : ∃ t ∈ Set.Ioo (1015.32600 : ℝ) (1016.55800 : ℝ), riemannZeta (1 / 2 + Complex.I * t) = 0 := by
  exact riemannZeta.exists_zero_of_zIntervalRS_certificate _ RHHeight1000.GramZero660.d218

#print axioms solution
