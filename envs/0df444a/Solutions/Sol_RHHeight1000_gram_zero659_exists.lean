-- Prove2me | solution 1 for RHHeight1000.gram_zero659_exists
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-19T16:40:15.094034+00:00
-- url     : https://prove2.me/submissions/0b5a77c0-8410-4c7a-8ae7-693dafde1e7b

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

namespace RHHeight1000.GramZero659
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

noncomputable def p177 :=
@Mathlib.Meta.NormNum.isRat_le_true.{0} Real
  (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField)) Real.linearOrder
  Real.instIsStrictOrderedRing
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
    true 5)
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
    true 5)
  (Int.ofNat 101409) (Int.ofNat 1015323) 100

noncomputable def p178 :=
@Mathlib.Meta.NormNum.isNNRat_nnratCast.{0} Real
  (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))
  (@FloorSemiring.instCharZero.{0} Real Real.semiring Real.partialOrder
    (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing))
  (NNRat.divNat 101409000
    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
      (@OfNat.ofNat.{0} Nat 10 (instOfNatNat 10)) 5))
  101409 100

noncomputable def p179 :=
@Mathlib.Meta.NormNum.isNNRat_divNat 101409000 101409000 101409
  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
    (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
    (@OfNat.ofNat.{0} Nat 10 (instOfNatNat 10)) 5)
  100000 100 (Mathlib.Meta.NormNum.IsNat.raw_refl 101409000)

noncomputable def p180 :=
@Mathlib.Meta.NormNum.isNNRat_div.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield)
  (@Nat.cast.{0} NNRat
    (@AddMonoidWithOne.toNatCast.{0} NNRat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat
          (@Semiring.toNonAssocSemiring.{0} NNRat
            (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))))))
    101409000)
  (@Nat.cast.{0} NNRat
    (@AddMonoidWithOne.toNatCast.{0} NNRat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat
          (@Semiring.toNonAssocSemiring.{0} NNRat
            (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))))))
    100000)

noncomputable def p181 :=
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
    101409000)
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

noncomputable def p182 :=
@Mathlib.Meta.NormNum.IsNat.to_isNNRat.{0} NNRat
  (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))
  (@Nat.cast.{0} NNRat
    (@AddMonoidWithOne.toNatCast.{0} NNRat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat
          (@Semiring.toNonAssocSemiring.{0} NNRat
            (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))))))
    101409000)
  101409000

noncomputable def p183 :=
p182
  (@Mathlib.Meta.NormNum.isNat_natCast.{0} NNRat
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat
        (@Semiring.toNonAssocSemiring.{0} NNRat
          (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield)))))
    101409000 101409000 (Mathlib.Meta.NormNum.IsNat.raw_refl 101409000))

noncomputable def p184 :=
@p181 101409000 1 101409 1 100000 100
  1000
  (@Eq.refl.{1} (NNRat → NNRat → NNRat)
    (@HMul.hMul.{0, 0, 0} NNRat NNRat NNRat
      (@instHMul.{0} NNRat
        (@Distrib.toMul.{0} NNRat
          (@instDistribOfSemiring.{0} NNRat
            (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield)))))))
  p183 (@p9 1 p11)

noncomputable def p185 :=
@p177 1000
  (@Mathlib.Meta.NormNum.IsNNRat.to_isRat.{0} Real
    (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
      true 5)
    101409 100
    (@Mathlib.Meta.NormNum.isNNRat_ofScientific_of_true.{0} Real
      (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)) 101409000
      5 101409 100
      (p178
        (p179 p4
          (@p180 101409 100
            (p184 (@Eq.refl.{1} Nat (Nat.mul 101409000 1))
              (@Eq.refl.{1} Nat 100000)))))))

noncomputable def p186 :=
@Mathlib.Meta.NormNum.isNNRat_nnratCast.{0} Real
  (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))
  (@FloorSemiring.instCharZero.{0} Real Real.semiring Real.partialOrder
    (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing))
  (NNRat.divNat 101532300
    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
      (@OfNat.ofNat.{0} Nat 10 (instOfNatNat 10)) 5))
  1015323 1000

noncomputable def p187 :=
@Mathlib.Meta.NormNum.isNNRat_divNat 101532300 101532300 1015323
  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
    (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
    (@OfNat.ofNat.{0} Nat 10 (instOfNatNat 10)) 5)
  100000 1000 (Mathlib.Meta.NormNum.IsNat.raw_refl 101532300)

noncomputable def p188 :=
@Mathlib.Meta.NormNum.isNNRat_div.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield)
  (@Nat.cast.{0} NNRat
    (@AddMonoidWithOne.toNatCast.{0} NNRat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat
          (@Semiring.toNonAssocSemiring.{0} NNRat
            (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))))))
    101532300)
  (@Nat.cast.{0} NNRat
    (@AddMonoidWithOne.toNatCast.{0} NNRat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat
          (@Semiring.toNonAssocSemiring.{0} NNRat
            (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))))))
    100000)

noncomputable def p189 :=
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
    101532300)
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

noncomputable def p190 :=
@Mathlib.Meta.NormNum.IsNat.to_isNNRat.{0} NNRat
  (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))
  (@Nat.cast.{0} NNRat
    (@AddMonoidWithOne.toNatCast.{0} NNRat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat
          (@Semiring.toNonAssocSemiring.{0} NNRat
            (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))))))
    101532300)
  101532300

noncomputable def p191 :=
p190
  (@Mathlib.Meta.NormNum.isNat_natCast.{0} NNRat
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat
        (@Semiring.toNonAssocSemiring.{0} NNRat
          (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield)))))
    101532300 101532300 (Mathlib.Meta.NormNum.IsNat.raw_refl 101532300))

noncomputable def p192 :=
@p189 101532300 1 1015323 1 100000 1000
  100
  (@Eq.refl.{1} (NNRat → NNRat → NNRat)
    (@HMul.hMul.{0, 0, 0} NNRat NNRat NNRat
      (@instHMul.{0} NNRat
        (@Distrib.toMul.{0} NNRat
          (@instDistribOfSemiring.{0} NNRat
            (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield)))))))
  p191 (@p9 1 p11)

noncomputable def p193 :=
p185
  (@Mathlib.Meta.NormNum.IsNNRat.to_isRat.{0} Real
    (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
      true 5)
    1015323 1000
    (@Mathlib.Meta.NormNum.isNNRat_ofScientific_of_true.{0} Real
      (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)) 101532300
      5 1015323 1000
      (p186
        (p187 p4
          (@p188 1015323 1000
            (p192 (@Eq.refl.{1} Nat (Nat.mul 101532300 1))
              (@Eq.refl.{1} Nat 100000)))))))

theorem d28 : @LE.le.{0} Real
  (@Preorder.toLE.{0} Real
    (@PartialOrder.toPreorder.{0} Real
      (@SemilatticeInf.toPartialOrder.{0} Real
        (@Lattice.toSemilatticeInf.{0} Real
          (@DistribLattice.toLattice.{0} Real (@instDistribLatticeOfLinearOrder.{0} Real Real.linearOrder))))))
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
    true 5)
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
    true 5) :=
p193 (Eq.refl true)

noncomputable def d29 :=
@NonemptyInterval.mk.{0} Real Real.instLE
  (@Prod.mk.{0, 0} Real Real
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
      true 5)
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
      true 5))
  d28

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

noncomputable def p2632 :=
nat_lit 1267650600228229401496703205376000000000000000

noncomputable def p2689 :=
nat_lit 3715469692580659200000000

noncomputable def p2694 :=
nat_lit 18889465931478580854784000000000000000

noncomputable def p2708 :=
nat_lit
  39269549297426202274627953190813615617062075509851135656156147621532437066659824993342760834661157342726800723004878364386749398774385139417224707831388179934939555033566573801472986402768684388462515827139319970167616786293934721803025338359040256570233635920150528000

noncomputable def p2711 :=
nat_lit
  6008241042506208948018076838194483189410497553007223755391890586094462871198953223981442407703157073437200510619746389751172658012480926330835380298202391530045751920135685791625366919623608711434764921552315955435645368302972012435862876768933159255245746295783030784000

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

noncomputable def p2820 :=
nat_lit 21778071482940061661655974875633165533184

noncomputable def p2846 :=
nat_lit 81165673924322027110400000000000000000000000

noncomputable def p2854 :=
nat_lit 243497021772966081331200000000000000000000000

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

noncomputable def p3406 :=
nat_lit 77371252455336267181195264

noncomputable def p3441 :=
nat_lit
  106352002277229487215352658285541407742310009375900930874240748115986981126606344351913283666201329978211874033038867377067676492944087568693592040852641253017373400345155447962475649007336027670197180202745856000

noncomputable def p3444 :=
nat_lit
  6062064129802080771275101522275860241311670534426353059831722642611257924216561628059057168973475808758076819883215440492857560097812991415534746328600551421990283819673860533861111993418153577201239271556513792000

noncomputable def p3467 :=
nat_lit
  6256000133954675718550156369737729867194706433876525345543573418587469478035667314818428450953019410483051413708168669239275087820240445217270120050155367824551376490891496938969155823960942804129245894279168000

noncomputable def p3469 :=
nat_lit
  957168020495065384938173924569872669680790084383108377868166733043882830139457099167219552995811969803906866297349806393609088436496788118242328367673771277156360603106399031662280841066024249031774621824712704000

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

noncomputable def p4831 :=
nat_lit 69206016000000000000000000

noncomputable def p5018 :=
nat_lit 73786976294838206464000000000000000

noncomputable def p5163 :=
nat_lit 842498333348457493583344221469363458551160763204392890034487820288000000000000000000000000000000000000000000000

noncomputable def p5168 :=
nat_lit 89202980794122492566142873090593446023921664000000000000000000000000000000

noncomputable def p5171 :=
nat_lit 9444732965739290427392000000000000000

noncomputable def p5216 :=
nat_lit 20282409603651670423947251286016000000000000000000000000000000

noncomputable def p5277 :=
nat_lit 13164036458569648337239753460458804039861886925068638906788872192

noncomputable def p5762 :=
nat_lit 47890485652059026823698344598447161988085597568237568

noncomputable def p5882 :=
nat_lit 210624583337114373395836055367340864637790190801098222508621955072

noncomputable def p5884 :=
nat_lit 842872547476238872097090864932670050990306517200981196800000000000000000000000000000000000000

noncomputable def p5892 :=
nat_lit 2528617642428716616291272594798010152970919551602943590400000000000000000000000000000000000000

noncomputable def p5920 :=
nat_lit 267727806768202049596103716975411200000000000000000000000

noncomputable def p5940 :=
nat_lit 87112285931760246646623899502532662132736

noncomputable def p7279 :=
nat_lit
  53631231719770388398296099992823384509917463282369573510894245774887056120294187907207497192667613710760127432745944203415015531247786279785734596024336384

noncomputable def p7287 :=
nat_lit
  12194330274671844653834364178879555881830461494785043558043581873536608354764709453594945715091765512343073949692994620685343654997219864477696

noncomputable def p7305 :=
nat_lit
  2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578097391210961403571828974157824

noncomputable def p7323 :=
nat_lit 316912650057057350374175801344

noncomputable def p7342 :=
nat_lit 59285549689505892056868344324448208820874232148807968788202283012051522375647232

noncomputable def p7351 :=
nat_lit 1146749307995035755805410447651043470398282494584140561868794419693461438044242404035009276555062843277312

noncomputable def p7449 :=
nat_lit 8958978968711216842229769122273777112486581988938598139599956403855167484720643781523509973086428463104

noncomputable def p7478 :=
nat_lit 2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376

noncomputable def p7486 :=
nat_lit 842498333348457493583344221469363458551160763204392890034487820288

noncomputable def p7523 :=
nat_lit 2993155353253689176481146537402947624255349848014848

noncomputable def p7541 :=
nat_lit 9671406556917033397649408

noncomputable def p7870 :=
nat_lit
  280528748176849183015425539339920495498509234119743350333152695834048405533944936582523226145133583973145537760862060363055975506138532699271526653087437574266421248000

noncomputable def p7873 :=
nat_lit
  42920898471057925001360107519007835811271912820320732600972362462609406046693575297126053600205438347891267277411895235547564252439195502988543577922377948862762450944000

noncomputable def p7956 :=
nat_lit 32592575621351777380295131014550050576823494298654980010178247189670100796213387298934358016

noncomputable def p8122 :=
nat_lit 340282366920938463463374607431768211456

noncomputable def p9769 :=
nat_lit
  1978643211784836272484020168157177520281050792809694719312504448743177800852254937362531208489944359916781371408129114714810920274454009679740369240815145343332854177189593088

noncomputable def p9972 :=
nat_lit
  460688772561223309599799143187044542348256984914116263229517370635452168260760357920669766257038423772151901248872539660616526444082616288154471954520592778765795328

noncomputable def p10241 :=
nat_lit
  667582338056245438668675204243831465490055283667469306154654509566051430133217024886826934189239674826355612291082932194574739779164547370092820033133599058893972435570631754625040768847067634603862769061368439492849485366996890270651430752103684361693971810642558976000

noncomputable def p10243 :=
nat_lit
  38052193269205990004114486641898393532933151169045750450815307045264931517593370418549135248786661465102269900591727135090760167412379200095290741888615146356956428827526010013627323824282855172420177836498001051092420665918822745427131552869910008616556393206625861632000

noncomputable def p10376 :=
nat_lit 401734511064747568885490523085290650630550748445698208825344000000000

noncomputable def p10380 :=
nat_lit 5444517870735015415413993718908291383296000000

noncomputable def p11263 :=
nat_lit
  421449425026245062161137734822778160352033234544485151135500978600616327240006200996093134633762175707582498363935964918318651382707695891823438796083487855385716340752307611

noncomputable def p11264 :=
nat_lit
  123665200736552267030251260509823595017565674550605919957031528046448612553265933585158200530621522494798835713008069669675682517153375604983773077550946583958303386074349568

noncomputable def p11265 :=
Enclosure.Real.IsNear
  (hardyZApproximantRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
      true 5))
  true p11263 p11264

noncomputable def p11266 :=
nat_lit
  1120384237328989664186099650593118574919850290932738068760546268358592709045085323424477796395899268360240092137383798044859648459360239587368487973332440282780986917852797494598879557521704608274384771010790454798672189845699

noncomputable def p11267 :=
nat_lit
  348550631928781186319004438918202757728028045062665538784180864874876326641169746603970599430862274653426414125902596361061453477005876652318421617716756480000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p11268 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZApproximantRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
      true 5))
  (hardyZApproximantRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
      true 5))
  true p11263

noncomputable def p11269 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
  (Zeta.RiemannSiegel.mainSumOfPhase
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
      true 5)
    12)

noncomputable def p11270 :=
@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p11271 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (@HPow.hPow.{0, 0, 0} Real Nat Real
    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
    (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)))
    12)
  (p11270
    (@Neg.neg.{0} Real Real.instNeg
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
        (@OfNat.ofNat.{0} Real 4
          (@instOfNatAtLeastTwo.{0} Real 4 Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))))))

noncomputable def p11272 :=
Real.sqrt
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p11273 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p11271
  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
        (Enclosure.sfrac false 12 1)))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Zeta.RiemannSiegel.correctionLinear
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
          (Enclosure.sfrac false 12 1)))
      (@Inv.inv.{0} Real Real.instInv p11272)))

noncomputable def p11274 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZApproximantRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
      true 5))
  (p11269 p11273) true p11263

noncomputable def p11275 :=
@BSN.floor_sqrt_eq_dec
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
    true 5)
  101409000 100000 12
  (Enclosure.sfrac_ofScientific_eq 101409000 5 100000 (Eq.refl true))

noncomputable def p11276 :=
@Enclosure.Real.IsNear.subLit_tf
  (Zeta.RiemannSiegel.mainSumOfPhase
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
      true 5)
    12)

noncomputable def p11277 :=
nat_lit
  15907543237759178868628018449978418463883971313167537944809897608123825189287049579156104727506766194158060561556527960558474599008560184008124102616935471861803134926378395

noncomputable def p11278 :=
nat_lit
  15396268462094668917733030162469983341566975565190647817022355798311657881388093989549305146897413196121074387085980418709948230361259715914212143572440282780986917852797494598879557521704608274384771010790454798672189845699

noncomputable def p11279 :=
nat_lit
  28961783958491623738617178451445640873200425431578578900553503482650287535031369217846762192354135713693959835121255602598110703928875740526323574966979091591917266385023251612430237696

noncomputable def p11280 :=
@p11276 p11273 225355441507 68719476736 217857
  68719476736 p11277 p11264 p11278
  p11267 p11279 p11263

noncomputable def p11281 :=
@Enclosure.Real.IsNear.of_eq
  (Zeta.RiemannSiegel.mainSumOfPhase
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
      true 5)
    12)

noncomputable def p11282 :=
@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
      true 5)
    12)

noncomputable def p11283 :=
p11282
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
      true 5)
    12)

noncomputable def p11284 :=
@p11281 p11283 true 225355441507 68719476736
  217857 68719476736
  (BSN.main_sum_of_phase_eq
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
      true 5)
    12)

noncomputable def p11285 :=
@Enclosure.Real.IsNear.addLit_tt
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
      true 5)
    12)

noncomputable def p11286 :=
@p11285
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
      true 5)
    12)

noncomputable def p11287 :=
@p11286 225355441507 137438953472 217857 137438953472
  225355441507 137438953472 217857 137438953472
  61945232079885181124608 225355441507 68719476736

noncomputable def p11288 :=
BSN.mainSumRS_step
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
      true 5))
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
    true 5)
  Real.cos BSN.quadSignNeg

noncomputable def p11289 :=
p11288 11 12 101409000 100000 286
  137438953472 68719476736 2305843009213693952 false 284541668614331
  3360

noncomputable def p11290 :=
p11289 341522969406 43 39675208392 8 true
  188197254497 204289 true 49218894706 7244019458077122842 1

noncomputable def p11291 :=
p11290 false 128719735636 true true 225355441507 217857
  BSN.abs_quadSignNeg (BSN.cos_quad_nat2 286 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 128719735636 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101409000 5 100000 (Eq.refl true))
  (Eq.refl true)

noncomputable def p11292 :=
BSN.mainSumRS_step2
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
      true 5))
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
    true 5)
  Real.cos Real.cos

noncomputable def p11293 :=
p11292 BSN.quadSignPos BSN.quadSignNeg 9 10 11 101409000
  100000 168 230 137438953472 68719476736

noncomputable def p11294 :=
p11293 2305843009213693952 false 284541668614331 3360
  316464885454 43 43462013224 8 329564216814 43
  41439403656

noncomputable def p11295 :=
p11294 8 true 176508054969 175257 true 112921725960
  true 11729261937 7244019458077122842 1 false

noncomputable def p11296 :=
p11295 93601490226 false false 136938760101 true true
  188197254497 204289 BSN.abs_quadSignPos
  (BSN.cos_quad_nat0 168 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 93601490226 137438953472)

noncomputable def p11297 :=
p11292 BSN.quadSignPos BSN.quadSignPos 7 8 9 101409000
  100000 24 100 137438953472 68719476736

noncomputable def p11298 :=
p11297 2305843009213693952 false 284541668614331 3360
  285796269294 43 48592008000 16 301984246446 43
  45812984488

noncomputable def p11299 :=
p11298 8 true 244983445266 142969 true 100143635485
  true 108675536857 7244019458077122842 1 false

noncomputable def p11300 :=
p11299 102540466992 false false 96665581562 false true
  176508054969 175257 BSN.abs_quadSignPos
  (BSN.cos_quad_nat0 24 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 102540466992 137438953472)

noncomputable def p11301 :=
BSN.mainSumRS_step2
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
      true 5))
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
    true 5)
  Real.sin Real.sin

noncomputable def p11302 :=
p11301 BSN.quadSignNeg BSN.quadSignNeg 5 6 7 101409000
  100000 161 61 137438953472 68719476736

noncomputable def p11303 :=
p11302 2305843009213693952 false 284541668614331 3360
  246257546308 43 56109217800 8 267443854420 43
  51947041624

noncomputable def p11304 :=
p11303 8 true 174881381209 106024 false 56288352002
  false 160325485939 7244019458077122842 1 false

noncomputable def p11305 :=
p11304 54727931382 true false 126359705833 true true
  244983445266 142969 BSN.abs_quadSignNeg
  (BSN.cos_quad_nat1 161 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 54727931382 137438953472)

noncomputable def p11306 :=
BSN.mainSumRS_step2
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
      true 5))
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
    true 5)
  Real.sin Real.cos

noncomputable def p11307 :=
p11306 BSN.quadSignPos BSN.quadSignNeg 3 4 5 101409000
  100000 423 278 137438953472 68719476736

noncomputable def p11308 :=
p11307 2305843009213693952 false 284541668614331 3360
  190530846192 42 68719476728 8 221199462352 42
  61464568544

noncomputable def p11309 :=
p11308 16 true 174248262197 62470 false 5363615280
  false 208474128077 7244019458077122842 1 false

noncomputable def p11310 :=
p11309 5362253932 false false 7410879299 true true
  174881381209 106024 BSN.abs_quadSignPos
  (BSN.cos_quad_nat3 423 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 5362253932 137438953472)

noncomputable def p11311 :=
p11292 BSN.quadSignNeg BSN.quadSignPos 1 2 3 101409000
  100000 870 608 137438953472 68719476736

noncomputable def p11312 :=
p11311 2305843009213693952 false 284541668614331 3360
  95265423088 42 97184016000 16 150992123216 42
  79350416784

noncomputable def p11313 :=
p11312 16 true 137438081768 3410 false 110870868074
  false 161795592627 7244019458077122842 1 false

noncomputable def p11314 :=
p11313 95092745830 true false 52707250025 false true
  174248262197 62470 BSN.abs_quadSignNeg
  (BSN.cos_quad_nat2 870 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 95092745830 137438953472)

noncomputable def p11315 :=
@Enclosure.Real.IsNear.recentre'
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
      true 5)
    1)

noncomputable def p11316 :=
@Enclosure.Real.IsNear.of_eq
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
      true 5)
    1)

noncomputable def p11317 :=
@p11316
  (Real.cos
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
        true 5)))
  true 17179760221

noncomputable def p11318 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
        true 5)))
  true 17179760221

noncomputable def p11319 :=
@Enclosure.Real.IsNear.cos_image
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
      true 5))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 35567708576791)
    (@Nat.cast.{0} Real Real.instNatCast 17179869184))
  false 35567708576791

noncomputable def p11320 :=
nat_lit 4056160372517714492813343537879152291172384380162507

noncomputable def p11321 :=
nat_lit 1959201404238033934675029952427591144942495334400

noncomputable def p11322 :=
@Enclosure.Real.IsNear.recentre'
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
      true 5))
  false p11320 p11321

noncomputable def p11323 :=
nat_lit 6920601600000000000000000

noncomputable def p11324 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 101409000 400000)
      (Real.log (Enclosure.sfrac false 41135151124000000 160000000000)))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 1 4)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 1 2) Real.pi)
        (Real.arctan
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@Nat.cast.{0} Real Real.instNatCast 100000)
            (@Nat.cast.{0} Real Real.instNatCast 202818000))))))

noncomputable def p11325 :=
nat_lit 514782773623165266736946352000000000000000000000

noncomputable def p11326 :=
nat_lit 3132216732762725792595984865558080000000000000000000

noncomputable def p11327 :=
@Enclosure.Real.IsNear.of_eq
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
      true 5))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (p11324 (Enclosure.sfrac false 101409000 200000))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 101409000 200000) (Real.log Real.pi)))
    (Enclosure.sfrac true p11325 p11326))
  false

noncomputable def p11328 :=
BSN.riemannSiegelThetaApproximant_two_zero_mk
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
    true 5)
  101409000 100000 41135151124000000 160000000000

noncomputable def p11329 :=
p11328 202818000 400000 200000 p11325
  p11326
  (Enclosure.sfrac_ofScientific_eq 101409000 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p11330 :=
@Enclosure.Real.IsNear.addLit_ft_p
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (p11324 (Enclosure.sfrac false 101409000 200000))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 101409000 200000) (Real.log Real.pi)))
  (Enclosure.sfrac true p11325 p11326) 3729544854930109181927
  1801439850948198400

noncomputable def p11331 :=
nat_lit 11681741872851017739302429389091958598576467014868020160000000000000000000

noncomputable def p11332 :=
@p11330 169140501727378637 p11323 p11325
  p11326 0 1 p11331 p11320
  p11321 169140501727378637 p11323

noncomputable def p11333 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (p11324 (Enclosure.sfrac false 101409000 200000))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 101409000 200000) (Real.log Real.pi))
  4775153803928113065959 1801439850948198400 127818142099 13200000000000000000

noncomputable def p11334 :=
nat_lit 51258474178847626566674493630054400

noncomputable def p11335 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 101409000 400000)
      (Real.log (Enclosure.sfrac false 41135151124000000 160000000000)))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 1 4)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 1 2) Real.pi)
        (Real.arctan
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@Nat.cast.{0} Real Real.instNatCast 100000)
            (@Nat.cast.{0} Real Real.instNatCast 202818000))))))

noncomputable def p11336 :=
@p11335 (Enclosure.sfrac false 101409000 200000)
  5688564873152142323687 1801439850948198400 127818142099 13200000000000000000
  101409000 200000 0

noncomputable def p11337 :=
nat_lit 955030760785622613191800000

noncomputable def p11338 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 101409000 400000)
    (Real.log (Enclosure.sfrac false 41135151124000000 160000000000)))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 1 4)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 1 2) Real.pi)
      (Real.arctan
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@Nat.cast.{0} Real Real.instNatCast 100000)
          (@Nat.cast.{0} Real Real.instNatCast 202818000)))))
  5689272074876120386887

noncomputable def p11339 :=
nat_lit 12809509321500440507225531293552869376

noncomputable def p11340 :=
@p11338 1801439850948198400 3842973953 400000000000000000
  884002154972579 2251799813685248 20000033 264000000000000000
  p11339 5688564873152142323687 1801439850948198400 127818142099

noncomputable def p11341 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 101409000 400000)
  (Real.log (Enclosure.sfrac false 41135151124000000 160000000000)) 101409000
  400000 0 1 56102240184560743 4503599627370496

noncomputable def p11342 :=
nat_lit 30842532713603250599738998784

noncomputable def p11343 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast 41135151124000000)
      (@Nat.cast.{0} Real Real.instNatCast 160000000000)))
  false p11342 p2333

noncomputable def p11344 :=
BSN.log_rat_reduce_isNear 41135151124000000 160000000000 17 82270302248000000
  41943040000000000 46296152575 68719476736 24973259072661432
  36028797018963968 26400000000 1000000000000000

noncomputable def p11345 :=
nat_lit
  889304114360151729201937386451450140470690434400971127635354486508213109516731913128406594089581860646215567133400937040965915084036811150216142697945862617563308143360031905159808591903611420409623723215813327571094141997982473278862966765754777600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p11346 :=
nat_lit
  33383882211655960090621465110021549328343646841068005204102568107500019395852820171958739256652618733742521202240417844266098606500830248925932729825010968629922019523444640023407934326013096310674566641038591259280170853046185821544839931033026560000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p11347 :=
nat_lit
  689911343588585341462525373386516541970866217032508509426922161100887856840899546050902758579452148867825855058284309292719879100051554856013730404229339447003616870574192377919758415382697472227185030375656064309302277295267078419251200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p11348 :=
BSN.log_dyadic_bound 20163631124000000 62106671124000000 12 11
  p11345 68719476736 26400000000 p11346 p11347
  46296152575 82270302248000000

noncomputable def p11349 :=
p11348 41943040000000000 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p11350 :=
@BSN.binarySplit_of_base11 (BSN.artanhP 20163631124000000) (BSN.artanhQ 62106671124000000)
  0 11 p11346 p11345 p11347
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p11351 :=
p11344 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p11349 (p11350 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

noncomputable def p11352 :=
@p11341 1250561 33000000000000000 5689272074876120386887
  1801439850948198400 3842973953 400000000000000000
  (Enclosure.Real.IsNear.const false 101409000 400000)
  (BSN.isNear_log_sfrac 41135151124000000 160000000000 56102240184560743
    4503599627370496 1250561 33000000000000000 false
    (@p11343 1000448800000000 p2422 56102240184560743
      4503599627370496 1250561 33000000000000000
      (p11351 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p11353 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 1 4)
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 1 2) Real.pi)
    (Real.arctan
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@Nat.cast.{0} Real Real.instNatCast 100000)
        (@Nat.cast.{0} Real Real.instNatCast 202818000))))
  1 4

noncomputable def p11354 :=
@p11353 0 1 884002154972579 562949953421312 20000033
  66000000000000000 884002154972579 2251799813685248 20000033
  264000000000000000 (Enclosure.Real.IsNear.const false 1 4)

noncomputable def p11355 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 1 2) Real.pi)
  (Real.arctan
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast 100000) (@Nat.cast.{0} Real Real.instNatCast 202818000)))
  884279719003555 562949953421312 1

noncomputable def p11356 :=
nat_lit 7593520690401501163552768

noncomputable def p11357 :=
@p11355 2000000000000000 4235291 8589934592 1
  3300000000 p11356 884002154972579 562949953421312 20000033
  66000000000000000
  (@p803 1 1000000000000000 884279719003555 562949953421312
    1 2000000000000000 (Enclosure.Real.IsNear.const false 1 2)
    BSN.pi_near_15 (Eq.refl true))

noncomputable def p11358 :=
BSN.arctan_dyadic_bound_f 100000 202818000 1 0 8589934592
  3300000000 0 1 1 0 1

noncomputable def p11359 :=
p11358 1 4235291 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)
  (@BSN.binarySplit_of_le (BSN.arctanEvenP 100000) (BSN.arctanEvenQ 202818000) 0
    0 (Eq.refl true))
  (@BSN.binarySplit_of_le (BSN.arctanOddP 100000) (BSN.arctanOddQ 202818000) 0 0
    (Eq.refl true))

noncomputable def p11360 :=
p11354
  (p11357
    (p11359 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p11361 :=
@p11333 7977363197311431 13743895347200 101409 6871947673600
  p11334 3729544854930109181927 1801439850948198400 169140501727378637
  p11323
  (@p11336 1 p11337 4775153803928113065959
    1801439850948198400 127818142099 13200000000000000000
    (@p11340 13200000000000000000 p11352 p11360
      (Eq.refl true) (Eq.refl true))
    (Enclosure.Real.IsNear.const false 101409000 200000) (Eq.refl true)
    (Eq.refl true))

noncomputable def p11362 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 101409000 200000) (Real.log Real.pi)
  101409000 200000 0 1 78665238759 68719476736

noncomputable def p11363 :=
p11361
  (@p11362 1 34359738368 7977363197311431 13743895347200
    101409 6871947673600
    (Enclosure.Real.IsNear.const false 101409000 200000) d91
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p11364 :=
@p11319 17179869184 421 17179869184 true 17179760221
  17179869184 1 3300000000
  (@p11322 169140501727378637 p11323 35567708576791
    17179869184 421 17179869184
    (@p11327 p11320 p11321 169140501727378637
      p11323
      (p11329 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p11332 (p11363 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p11325 p11326)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p11365 :=
nat_lit 8818072708239190279585792

noncomputable def p11366 :=
BSN.cos_reduce2
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 35567708576791)
    (@Nat.cast.{0} Real Real.instNatCast 17179869184))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast p11365)
    (@Nat.cast.{0} Real Real.instNatCast p2333))
  226375608064910080 72057594037927936 false

noncomputable def p11367 :=
BSN.sin_reduce_arg_pos_rat_q2 35567708576791 17179869184 226375608064910080
  72057594037927936 329 p11365 p2333
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p11368 :=
BSN.cos_dyadic_bound_f 125312350124 35184372088832 1 0 17179869184
  6606445313 0 1 1 0 1

noncomputable def p11369 :=
p11368 1 17179760221 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (@BSN.binarySplit_of_le (BSN.cosEvenP 125312350124) (BSN.cosEvenQ 35184372088832) 0
    0 (Eq.refl true))

noncomputable def p11370 :=
p11369
  (@BSN.binarySplit_of_le (BSN.cosOddP 125312350124) (BSN.cosOddQ 35184372088832) 0
    0 (Eq.refl true))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p11371 :=
@BSN.cos_arg_round false 17179760221 17179869184 p11365
  p2333 125312350124 35184372088832 6606445313 6600000000
  p11370 (Eq.refl true)

noncomputable def p11372 :=
p11366 17179760221 17179869184 329 1000000000000000
  6600000000 3300000000 p11367 BSN.pi_near_15 p11371
  (Eq.refl true) (Eq.refl true)

noncomputable def p11373 :=
@p11317 17179869184 5494061989 221459251200000000
  (BSN.main_sum_rs_one
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
      true 5))
  (@p11318 17179869184 1406479869184 56693568307200000000
    17179760221 17179869184 5494061989 221459251200000000
    (p11364 (Enclosure.sfrac_false_div 35567708576791 17179869184)
      (p11372 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p11374 :=
@p11315 true 17179760221 17179869184 5494061989
  221459251200000000 137438081768 137438953472 3410 137438953472
  p11373 (Eq.refl true)

noncomputable def p11375 :=
p11314 BSN.abs_quadSignPos (BSN.cos_quad_nat0 608 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 52707250025 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101409000 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true) p11374
  (@p11322 169140501727378637 p11323 284541668614331
    137438953472 3360 137438953472
    (@p11327 p11320 p11321 169140501727378637
      p11323
      (p11329 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p11332 (p11363 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p11325 p11326)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p11376 :=
nat_lit
  384046395351783853417505577465968504606374276302721868205936608887397927449124052831799700813464240397588610385802646575609390972068861382656

noncomputable def p11377 :=
nat_lit
  3449922783030345132863912139535963496865374105277231919038897977709260152383063307382440152506234890885736995540004950112808711294976

noncomputable def p11378 :=
nat_lit
  2329490017520757902002882633686124073618944166600588363921444742288625118309672551966406215373077103134631209873548464134065583117149757050880

noncomputable def p11379 :=
BSN.cos_dyadic_bound_f 110870868074 137438953472 4 3 137438953472
  68719476736 p11376 p2457 p11377
  p11378 p2460

noncomputable def p11380 :=
@BSN.binarySplit_of_base3 (BSN.cosEvenP 110870868074) (BSN.cosEvenQ 137438953472) 0
  3 p11376 p2457 p11377 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p11381 :=
p11379 p11377 95092745830 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p11380 (Eq.refl true))

noncomputable def p11382 :=
@BSN.binarySplit_of_base3 (BSN.cosOddP 110870868074) (BSN.cosOddQ 137438953472) 0
  3 p11378 p2460 p11377 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p11383 :=
nat_lit
  1743281272235585650912664110923775159279597674947762807405960427836036929144944208719530836829375344520690762676331187680843972196890659354801

noncomputable def p11384 :=
nat_lit
  321810525928674193014228059151998785778207909131762640944251080644856517124122448525901634579514090479759226033465809295599849701996721

noncomputable def p11385 :=
nat_lit
  10567853785102806749892813504178661169643435676796273020844424460137201703216068941342084983077193798119243076729832255431745996375871061588145

noncomputable def p11386 :=
BSN.cos_dyadic_bound_f 161795592627 137438953472 4 3 137438953472
  68719476736 p11383 p2457 p11384
  p11385 p2460

noncomputable def p11387 :=
@BSN.binarySplit_of_base3 (BSN.cosEvenP 161795592627) (BSN.cosEvenQ 137438953472) 0
  3 p11383 p2457 p11384 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p11388 :=
p11386 p11384 52707250025 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p11387 (Eq.refl true))

noncomputable def p11389 :=
@BSN.binarySplit_of_base3 (BSN.cosOddP 161795592627) (BSN.cosOddQ 137438953472) 0
  3 p11385 p2460 p11384 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p11390 :=
p11375 d93 d95 d97 d99 d103
  (p11381 (p11382 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p11388 (p11389 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p11391 :=
p11310 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 278 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 7410879299 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101409000 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p11390 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p11322 169140501727378637 p11323 284541668614331
    137438953472 3360 137438953472
    (@p11327 p11320 p11321 169140501727378637
      p11323
      (p11329 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p11332 (p11363 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p11325 p11326)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p11392 :=
nat_lit 827619047546798030560015386352066560000

noncomputable def p11393 :=
BSN.sin_dyadic_bound_f 5363615280 137438953472 2 1 137438953472
  68719476736 p11392 p3178 p11392
  p11392 p3179

noncomputable def p11394 :=
@BSN.binarySplit_of_base (BSN.sinEvenP 5363615280) (BSN.sinEvenQ 137438953472) 0
  1 p11392 p3178 p11392 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p11395 :=
p11393 p11392 5362253932 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p11394 (Eq.refl true))

noncomputable def p11396 :=
@BSN.binarySplit_of_base (BSN.sinOddP 5363615280) (BSN.sinOddQ 137438953472) 0 1
  p11392 p3179 p11392 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p11397 :=
nat_lit
  75041593253934602248489589898556484538429133100571547393945720832681774433770770017850775275060364314577367396675079022414268374510086639908249440207349339877564957494046629744724760067915841

noncomputable def p11398 :=
nat_lit
  12730183324673261132471289574971376252805491902595823070334347136027587973066882624069381180484657930985151729551460635940505606254300260817636583625025284253622464517853408573341761

noncomputable def p11399 :=
nat_lit
  763820465143912523004127014058073156271530413158410563892975945902288580161674441910019888096675028149953636092461453844770105203802468970203260183412941406582011710903361098789674595615850561

noncomputable def p11400 :=
BSN.cos_dyadic_bound_f 208474128077 137438953472 5 4 137438953472
  68719476736 p11397 p2495 p11398
  p11399 p2498

noncomputable def p11401 :=
@BSN.binarySplit_of_base4 (BSN.cosEvenP 208474128077) (BSN.cosEvenQ 137438953472) 0
  4 p11397 p2495 p11398 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p11402 :=
p11400 p11398 7410879299 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p11401 (Eq.refl true))

noncomputable def p11403 :=
@BSN.binarySplit_of_base4 (BSN.cosOddP 208474128077) (BSN.cosOddQ 137438953472) 0
  4 p11399 p2498 p11398 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p11404 :=
p11391 d105 d107 d109 d111 d103
  (p11395 (p11396 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p11402 (p11403 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p11405 :=
p11305 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 61 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 126359705833 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101409000 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p11404 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p11322 169140501727378637 p11323 284541668614331
    137438953472 3360 137438953472
    (@p11327 p11320 p11321 169140501727378637
      p11323
      (p11329 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p11332 (p11363 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p11325 p11326)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p11406 :=
nat_lit 10831767270684247816452338617750138182117371406103184528261110496822649185016908634860028160

noncomputable def p11407 :=
nat_lit 100773947114595545818588330310122342058943196110079199902037845542076161999995240448256

noncomputable def p11408 :=
nat_lit 28368751122544368269348609141572716945563115393667019350550686097071298789829617860910776576

noncomputable def p11409 :=
BSN.sin_dyadic_bound_f 56288352002 137438953472 3 2 137438953472
  68719476736 p11406 p2477 p11407
  p11408 p2480

noncomputable def p11410 :=
@BSN.binarySplit_of_base2 (BSN.sinEvenP 56288352002) (BSN.sinEvenQ 137438953472) 0
  2 p11406 p2477 p11407 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p11411 :=
p11409 p11407 54727931382 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p11410 (Eq.refl true))

noncomputable def p11412 :=
@BSN.binarySplit_of_base2 (BSN.sinOddP 56288352002) (BSN.sinOddQ 137438953472) 0
  2 p11408 p2480 p11407 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p11413 :=
nat_lit
  4367711332419818328188220310498719909189663281426343915472322020922589397622461397857817307394272653653753317641168732816414206079537069311921

noncomputable def p11414 :=
nat_lit
  288423590539358578607049533710021243500596039012714439275265428742544485827372477186738306092191957911936453722412284262261371151206321

noncomputable def p11415 :=
nat_lit
  21830293923071624917819306377780801388740905595928419775768069419423016279668367966424971692833121737403109435377621199595091275278044666152881

noncomputable def p11416 :=
BSN.sin_dyadic_bound_f 160325485939 137438953472 4 3 137438953472
  68719476736 p11413 p2504 p11414
  p11415 p2507

noncomputable def p11417 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 160325485939) (BSN.sinEvenQ 137438953472) 0
  3 p11413 p2504 p11414 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p11418 :=
p11416 p11414 126359705833 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p11417 (Eq.refl true))

noncomputable def p11419 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 160325485939) (BSN.sinOddQ 137438953472) 0
  3 p11415 p2507 p11414 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p11420 :=
p11405 d113 d115 d117 d119 d103
  (p11411 (p11412 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p11418 (p11419 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p11421 :=
p11300 BSN.abs_quadSignPos (BSN.cos_quad_nat0 100 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 96665581562 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101409000 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p11420 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p11322 169140501727378637 p11323 284541668614331
    137438953472 3360 137438953472
    (@p11327 p11320 p11321 169140501727378637
      p11323
      (p11329 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p11332 (p11363 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p11325 p11326)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p11422 :=
nat_lit
  255605806251956867059292861376559411382427939129498647924721345792803674219068277687089707864923977011346686625289466296405084824018740640625

noncomputable def p11423 :=
nat_lit
  1017373077859060719166654430937512879175554418397283223126348892727244738331712564872417873114957048880813554472705953971445556640625

noncomputable def p11424 :=
nat_lit
  1550501798514682079564446652935160264040633677714601536832174130315988780363062849466482998926548818401760829567488220675788951107123406240625

noncomputable def p11425 :=
BSN.cos_dyadic_bound_f 100143635485 137438953472 4 3 137438953472
  68719476736 p11422 p2457 p11423
  p11424 p2460

noncomputable def p11426 :=
@BSN.binarySplit_of_base3 (BSN.cosEvenP 100143635485) (BSN.cosEvenQ 137438953472) 0
  3 p11422 p2457 p11423 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p11427 :=
p11425 p11423 102540466992 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p11426 (Eq.refl true))

noncomputable def p11428 :=
@BSN.binarySplit_of_base3 (BSN.cosOddP 100143635485) (BSN.cosOddQ 137438953472) 0
  3 p11424 p2460 p11423 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p11429 :=
nat_lit
  354513406826824720834566550777551607654308307255480589391870904355220311271442485832791748750811262558626854070172929006094738597052315128481

noncomputable def p11430 :=
nat_lit
  2713823078364832363743497492218772070221266583800500272426744539496178555193451504602239122122076675481009359299166013685920404656801

noncomputable def p11431 :=
nat_lit
  2150381098125143066694519629025499797543578887600342825917148510137024083383677548604593767778857853013844786063154609221463789590336008671905

noncomputable def p11432 :=
BSN.cos_dyadic_bound_f 108675536857 137438953472 4 3 137438953472
  68719476736 p11429 p2457 p11430
  p11431 p2460

noncomputable def p11433 :=
@BSN.binarySplit_of_base3 (BSN.cosEvenP 108675536857) (BSN.cosEvenQ 137438953472) 0
  3 p11429 p2457 p11430 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p11434 :=
p11432 p11430 96665581562 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p11433 (Eq.refl true))

noncomputable def p11435 :=
@BSN.binarySplit_of_base3 (BSN.cosOddP 108675536857) (BSN.cosOddQ 137438953472) 0
  3 p11431 p2460 p11430 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p11436 :=
p11421 d121 d123 d125 d127 d103
  (p11427 (p11428 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p11434 (p11435 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p11437 :=
p11296 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 230 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 136938760101 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101409000 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p11436 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p11322 169140501727378637 p11323 284541668614331
    137438953472 3360 137438953472
    (@p11327 p11320 p11321 169140501727378637
      p11323
      (p11329 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p11332 (p11363 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p11325 p11326)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p11438 :=
nat_lit
  413268456013898178088136114773955827946205288420202212877280663147163394191242627530906725909064004479646158462124122885946704285138944000000

noncomputable def p11439 :=
nat_lit
  4298630248126938216308156757639418762749345162217618811944802182510683203628967671943319652727432105922840112267490492416000000000000

noncomputable def p11440 :=
nat_lit
  2506708697918387455673125195108278818008026094856750646992449900524841283172693236029116474033879792424495943834483781849225381988112793600000

noncomputable def p11441 :=
BSN.cos_dyadic_bound_f 112921725960 137438953472 4 3 137438953472
  68719476736 p11438 p2457 p11439
  p11440 p2460

noncomputable def p11442 :=
@BSN.binarySplit_of_base3 (BSN.cosEvenP 112921725960) (BSN.cosEvenQ 137438953472) 0
  3 p11438 p2457 p11439 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p11443 :=
p11441 p11439 93601490226 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p11442 (Eq.refl true))

noncomputable def p11444 :=
@BSN.binarySplit_of_base3 (BSN.cosOddP 112921725960) (BSN.cosOddQ 137438953472) 0
  3 p11440 p2460 p11439 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p11445 :=
nat_lit 18927041749539098190234721354509130496961

noncomputable def p11446 :=
BSN.cos_dyadic_bound_f 11729261937 137438953472 2 1 137438953472
  68719476736 p11445 p2486 p11445
  p11445 p2487

noncomputable def p11447 :=
@BSN.binarySplit_of_base (BSN.cosEvenP 11729261937) (BSN.cosEvenQ 137438953472) 0
  1 p11445 p2486 p11445 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p11448 :=
p11446 p11445 136938760101 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p11447 (Eq.refl true))

noncomputable def p11449 :=
@BSN.binarySplit_of_base (BSN.cosOddP 11729261937) (BSN.cosOddQ 137438953472) 0
  1 p11445 p2487 p11445 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p11450 :=
p11437 d129 d131 d133 d135 d103
  (p11443 (p11444 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p11448 (p11449 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p11451 :=
p11291
  (p11450 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p11322 169140501727378637 p11323 284541668614331
    137438953472 3360 137438953472
    (@p11327 p11320 p11321 169140501727378637
      p11323
      (p11329 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p11332 (p11363 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p11325 p11326)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p11452 :=
nat_lit 3517874308312298541899213669908386080049129683740247320391488096918310301482935131485552896

noncomputable def p11453 :=
nat_lit 34439342637068448879478757631535683082335131320653034706258597952740200444511900713216

noncomputable def p11454 :=
nat_lit 10553554046251621488799882052209895168781224380958100655105051773559025424047916370655232256

noncomputable def p11455 :=
BSN.cos_dyadic_bound_f 49218894706 137438953472 3 2 137438953472
  68719476736 p11452 p2466 p11453
  p11454 p2469

noncomputable def p11456 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP 49218894706) (BSN.cosEvenQ 137438953472) 0
  2 p11452 p2466 p11453 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p11457 :=
p11455 p11453 128719735636 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p11456 (Eq.refl true))

noncomputable def p11458 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP 49218894706) (BSN.cosOddQ 137438953472) 0
  2 p11454 p2469 p11453 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p11459 :=
p11451 d137 d139 d103
  (p11457 (p11458 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true) (Eq.refl true)

noncomputable def p11460 :=
@p11280 p11264 p11266 p11267
  (p11284
    (@p11287 217857 68719476736
      (p11459 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (p11459 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true) (Eq.refl true)))

noncomputable def p11461 :=
@Enclosure.Real.IsNear.mulLit_ff p11271
  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
        (Enclosure.sfrac false 12 1)))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Zeta.RiemannSiegel.correctionLinear
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
          (Enclosure.sfrac false 12 1)))
      (@Inv.inv.{0} Real Real.instInv p11272)))

noncomputable def p11462 :=
nat_lit
  211221144594667145906363679770500315225990625314300231392714517651205814708605831492977163036491335391060005690129178564741313642949563369379441235209869221727227185

noncomputable def p11463 :=
nat_lit
  63807933835935922708355747286903003546732090778176210455730725640680982165263963449912245752980678305682373806450205424833690527177083246174559407617489326206285709870276539889715013650267454231249036605156386104447

noncomputable def p11464 :=
nat_lit
  405766339889705630856338468052217221967908606238972324393900186841930643004795707068371818669678497423215785676034396003304810120032490990495334400000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p11465 :=
@p11461 75312267 268435456 1 8589934592
  p11462 p9972 p11463 p11464
  p11277 p11264 p11278

noncomputable def p11466 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HPow.hPow.{0, 0, 0} Real Nat Real
    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
    (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)))
    12)
  (p11270
    (@Neg.neg.{0} Real Real.instNeg
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
        (@OfNat.ofNat.{0} Real 4
          (@instOfNatAtLeastTwo.{0} Real 4 Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))))))

noncomputable def p11467 :=
@p11466 1 1 0 1 75312267 268435456
  1 8589934592 75312267 268435456 1

noncomputable def p11468 :=
@Enclosure.Real.IsNear.of_eq
  (p11270
    (@Neg.neg.{0} Real Real.instNeg
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
        (@OfNat.ofNat.{0} Real 4
          (@instOfNatAtLeastTwo.{0} Real 4 Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))))))

noncomputable def p11469 :=
BSN.rpow_neg_quarter_mk
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p11470 :=
p11469
  (BSN.t_div_two_pi_nonneg
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
      true 5)
    101409000 100000
    (Enclosure.sfrac_ofScientific_eq 101409000 5 100000 (Eq.refl true)))

noncomputable def p11471 :=
@Enclosure.Real.IsNear.recentre' (@Inv.inv.{0} Real Real.instInv (Real.sqrt p11272)) false
  4819985088 17179869184 2 17179869184 75312267 268435456

noncomputable def p11472 :=
@Enclosure.Real.IsNear.recentre' (Real.sqrt p11272) false 61234194672
  17179869184 6 17179869184 3827137167 1073741824 3
  8589934592

noncomputable def p11473 :=
@Enclosure.Real.IsNear.sqrt_image
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p11474 :=
@Enclosure.Real.IsNear.of_eq
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p11475 :=
@p11474
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 101409000 100000)
    (@Inv.inv.{0} Real Real.instInv
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)))
  false 277278684194127

noncomputable def p11476 :=
@p11475 1717986918400 101409 1717986918400
  (BSN.t_div_two_pi_mk
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
      true 5)
    101409000 100000
    (Enclosure.sfrac_ofScientific_eq 101409000 5 100000 (Eq.refl true)))

noncomputable def p11477 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 101409000 100000)
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi))
  101409000 100000 0

noncomputable def p11478 :=
@p11477 1 2734261103 17179869184 1 17179869184
  277278684194127 1717986918400 101409 1717986918400
  (Enclosure.Real.IsNear.const false 101409000 100000) d142

noncomputable def p11479 :=
@p11473 277278684194127 1717986918400 101409 1717986918400
  109128496739 109128496780 8589934592
  (p11476 (p11478 (Eq.refl true))) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p11480 :=
@Enclosure.Real.IsNear.recentre' p11272 false 218256993519 17179869184
  41 17179869184 218256993519 17179869184 41 17179869184
  (p11479 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p11481 :=
@Enclosure.Real.IsNear.sqrt_image p11272 218256993519 17179869184 41
  17179869184 30617097333 30617097339 8589934592
  (p11480 (Eq.refl true)) (Eq.refl true) (Eq.refl true)

noncomputable def p11482 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt p11272) 3827137167 1073741824
  3 8589934592 2409992543 2409992545 8589934592
  (p11472
    (p11481 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p11483 :=
@p11468 (@Inv.inv.{0} Real Real.instInv (Real.sqrt p11272)) false
  75312267 268435456 1 8589934592 p11470
  (@p11471 1 8589934592
    (p11482 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p11484 :=
@Enclosure.Real.IsNear.addLit_ft_p
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
      (Enclosure.sfrac false 12 1)))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Zeta.RiemannSiegel.correctionLinear
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
        (Enclosure.sfrac false 12 1)))
    (@Inv.inv.{0} Real Real.instInv p11272))
  33886121248593832905

noncomputable def p11485 :=
nat_lit 9907919180215091200000000

noncomputable def p11486 :=
nat_lit
  346755172592331046309437468281519663875903815427013597629155079162732935203105374436524253306746608275669132578312790359531824459959392438492428396456294246855375

noncomputable def p11487 :=
nat_lit
  1557139008069502382475405295779560042317481105428091609952290677023664508224098585982500473881518010741809413333855338978129877782323952647167151617489326206285709870276539889715013650267454231249036605156386104447

noncomputable def p11488 :=
nat_lit
  15585369589175297862546224644595659295218156923468970435914789203829237041620737817445604240842467450098116764593845273135603312482714624157423307955588165690488198812193763461263523840

noncomputable def p11489 :=
@p11484 73786976294838206464 1520027127499788513 p11485
  p11486 p9972 p11487 p11464
  p11488 p11462 p9972 p11463

noncomputable def p11490 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (@Inv.inv.{0} Real Real.instInv
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
          (Enclosure.sfrac false 12 1)))))

noncomputable def p11491 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
        (Enclosure.sfrac false 12 1))
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
        (Enclosure.sfrac false 12 1)))
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
      (Enclosure.sfrac false 12 1)))

noncomputable def p11492 :=
@Enclosure.Real.IsNear.of_eq
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
      (Enclosure.sfrac false 12 1)))
  (p11490
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p11491 (Enclosure.sfrac false 1 16)))))

noncomputable def p11493 :=
BSN.cos_two_pi_p_ne_zero_mk
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
    true 5)
  101409000 100000 12
  (Enclosure.sfrac_ofScientific_eq 101409000 5 100000 (Eq.refl true))

noncomputable def p11494 :=
@Enclosure.Real.IsNear.mulLit_tt
  (@Inv.inv.{0} Real Real.instInv
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
          (Enclosure.sfrac false 12 1)))))

noncomputable def p11495 :=
@p11494
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p11491 (Enclosure.sfrac false 1 16))))
  60569408943

noncomputable def p11496 :=
@p11495 17179869184 3285 17179869184 559459335
  4294967296 8072186989 221459251200000000 33886121248593832905
  73786976294838206464 1520027127499788513 p11485

noncomputable def p11497 :=
@Enclosure.Real.IsNear.of_eq
  (@Inv.inv.{0} Real Real.instInv
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
          (Enclosure.sfrac false 12 1)))))

noncomputable def p11498 :=
@Inv.inv.{0} Real Real.instInv
  (@Neg.neg.{0} Real Real.instNeg
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
          (Enclosure.sfrac false 12 1)))))

noncomputable def p11499 :=
@p11497 (@Neg.neg.{0} Real Real.instNeg p11498) true 60569408943
  17179869184 3285 17179869184
  (BSN.inv_eq_neg_inv_neg
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
          (Enclosure.sfrac false 12 1)))))

noncomputable def p11500 :=
@Enclosure.Real.IsNear.inv_image
  (@Neg.neg.{0} Real Real.instNeg
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
          (Enclosure.sfrac false 12 1)))))

noncomputable def p11501 :=
@Enclosure.Real.IsNear.neg
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
        (Enclosure.sfrac false 12 1))))
  true

noncomputable def p11502 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
        (Enclosure.sfrac false 12 1))))
  true

noncomputable def p11503 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
      (Enclosure.sfrac false 12 1)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 76017515233)
    (@Nat.cast.{0} Real Real.instNatCast 17179869184))
  false

noncomputable def p11504 :=
nat_lit 10698514164997800001570605

noncomputable def p11505 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
      (Enclosure.sfrac false 12 1)))
  false p11504

noncomputable def p11506 :=
nat_lit 1106429195696673362322881759

noncomputable def p11507 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
    (Enclosure.sfrac false 12 1))
  884279719003555 140737488355328 1

noncomputable def p11508 :=
@Enclosure.Real.IsNear.subLit_ff_p p11272 (Enclosure.sfrac false 12 1)
  218256993519 17179869184 41 17179869184 12 1 0

noncomputable def p11509 :=
@p11507 500000000000000 12098563311 17179869184 41
  17179869184 p11504 p2602 p11506
  p5018 d141
  (@p11508 1 12098563311 12098563311 17179869184 41
    17179869184 (p11480 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p11510 :=
@p11503 76017515233 17179869184 259 17179869184 true
  4872887326 17179869184 1 3300000000
  (@p11505 p2602 p11506 p5018
    76017515233 17179869184 259 17179869184
    (p11509 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div 76017515233 17179869184)

noncomputable def p11511 :=
nat_lit 3177071838855812599026548736

noncomputable def p11512 :=
BSN.cos_reduce2
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 76017515233)
    (@Nat.cast.{0} Real Real.instNatCast 17179869184))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast p11511)
    (@Nat.cast.{0} Real Real.instNatCast p2333))
  226375608064910080 72057594037927936 false

noncomputable def p11513 :=
BSN.sin_reduce_arg_pos_rat_q2 76017515233 17179869184 226375608064910080
  72057594037927936 0 p11511 p2333 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p11514 :=
nat_lit
  195080386872251154126863562989406888227219654168618552081438427656977593286372942417476526091360237871840535292611032369984897973885204021910486336752038092889664769600401

noncomputable def p11515 :=
nat_lit
  71740898924386370894123442990310039584617506550999196328344749873430770484010493896405104015708544293767468185561099998811776227555182209483413880961139838610680721

noncomputable def p11516 :=
nat_lit
  1182216004097922936467495315136025511879166801158554416185285742534737590813678882431464512565317808505080676811820451232875065939682742304584898037165399142065337754561425

noncomputable def p11517 :=
BSN.cos_dyadic_bound_f 45148906321739 35184372088832 4 3 17179869184
  6606445313 p11514 p2613 p11515
  p11516 p2616

noncomputable def p11518 :=
@BSN.binarySplit_of_base3 (BSN.cosEvenP 45148906321739) (BSN.cosEvenQ 35184372088832) 0
  3 p11514 p2613 p11515 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p11519 :=
p11517 p11515 4872887326 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p11518 (Eq.refl true))

noncomputable def p11520 :=
@BSN.binarySplit_of_base3 (BSN.cosOddP 45148906321739) (BSN.cosOddQ 35184372088832) 0
  3 p11516 p2616 p11515 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p11521 :=
@BSN.cos_arg_round false 4872887326 17179869184 p11511
  p2333 45148906321739 35184372088832 6606445313 6600000000
  (p11519 (p11520 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p11522 :=
p11512 4872887326 17179869184 0 1000000000000000
  6600000000 3300000000 p11513 BSN.pi_near_15 p11521
  (Eq.refl true) (Eq.refl true)

noncomputable def p11523 :=
@p11501 2436443663 8589934592 3405780739 221459251200000000
  (@p11502 4872887326 17179869184 871879869184
    56693568307200000000 2436443663 8589934592 3405780739
    221459251200000000
    (p11510 (p11522 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p11524 :=
@p11500 2436443663 8589934592 3405780739 221459251200000000
  30284702829 30284706114 8589934592 p11523
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p11525 :=
@Enclosure.Real.IsNear.recentre' p11498 false 60569408943 17179869184
  3285 17179869184 60569408943 17179869184 3285 17179869184
  (p11524 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p11526 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p11491 (Enclosure.sfrac false 1 16))))
  true

noncomputable def p11527 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p11491 (Enclosure.sfrac false 1 16)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Neg.neg.{0} Real Real.instNeg (@Nat.cast.{0} Real Real.instNatCast 7307572493))
    (@Nat.cast.{0} Real Real.instNatCast 4294967296))
  true

noncomputable def p11528 :=
nat_lit 70674504525007387945854637770658045

noncomputable def p11529 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p11491 (Enclosure.sfrac false 1 16)))
  true p11528

noncomputable def p11530 :=
nat_lit 45780712621736062002677229414110482457

noncomputable def p11531 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (p11491 (Enclosure.sfrac false 1 16)) 884279719003555
  140737488355328 1

noncomputable def p11532 :=
@Enclosure.Real.IsNear.subLit_tf
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
        (Enclosure.sfrac false 12 1))
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
        (Enclosure.sfrac false 12 1)))
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
      (Enclosure.sfrac false 12 1)))

noncomputable def p11533 :=
@p11532 (Enclosure.sfrac false 1 16) 61476500807046625503
  295147905179352825856 1696456829727 295147905179352825856 1 16
  0

noncomputable def p11534 :=
@Enclosure.Real.IsNear.subLit_ff_n
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
      (Enclosure.sfrac false 12 1))
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
      (Enclosure.sfrac false 12 1)))
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
    (Enclosure.sfrac false 12 1))
  146375234190275282721

noncomputable def p11535 :=
nat_lit 1056158241755131451530178199552

noncomputable def p11536 :=
@p11534 295147905179352825856 992082193183 295147905179352825856
  12098563311 17179869184 41 17179869184 p11535
  61476500807046625503 295147905179352825856 1696456829727

noncomputable def p11537 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
    (Enclosure.sfrac false 12 1))
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
    (Enclosure.sfrac false 12 1))
  12098563311 17179869184 41

noncomputable def p11538 :=
@p11537 17179869184 12098563311 17179869184 41
  17179869184 146375234190275282721 295147905179352825856 992082193183
  295147905179352825856
  (@p11508 1 12098563311 12098563311 17179869184 41
    17179869184 (p11480 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p11539 :=
p11538
  (@p11508 1 12098563311 12098563311 17179869184 41
    17179869184 (p11480 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p11540 :=
@p11536 295147905179352825856 (p11539 (Eq.refl true))
  (@p11508 1 12098563311 12098563311 17179869184 41
    17179869184 (p11480 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p11541 :=
@p11531 500000000000000 79923244880756177119 295147905179352825856
  1696456829727 295147905179352825856 p11528 p2630
  p11530 p2632 d141
  (@p11533 1 1278771918092098833904 79923244880756177119
    295147905179352825856 1696456829727 295147905179352825856
    (p11540 (Eq.refl true) (Eq.refl true))
    (Enclosure.Real.IsNear.const false 1 16) (Eq.refl true)
    (Eq.refl true))

noncomputable def p11542 :=
@p11527 7307572493 4294967296 621 17179869184 true
  1118918670 8589934592 1 3300000000
  (@p11529 p2630 p11530 p2632
    7307572493 4294967296 621 17179869184
    (p11541 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_true_div 7307572493 4294967296)

noncomputable def p11543 :=
nat_lit
  98442288130450741290151042755514854201794060396520774363063889035736009507736708783818912112443984154667577387253379437720539843480361917561349964769316511307728598081

noncomputable def p11544 :=
nat_lit
  66125674931446364883220190403030451630829059735107533129817388183302431131591093445872755149350177041165138745366760276089569355120271082290533860852586689601

noncomputable def p11545 :=
nat_lit
  1000785849102631209859325576190361754648633404422448512263839540209334356056940859158642696580649905505450806352437856613580696905575951883817507719951947627907681268801

noncomputable def p11546 :=
BSN.cos_dyadic_bound_t 7307572493 4294967296 5 4 8589934592
  3300000000 p11543 p7870 p11544
  p11545 p7873

noncomputable def p11547 :=
@BSN.binarySplit_of_base4 (BSN.cosEvenP 7307572493) (BSN.cosEvenQ 4294967296) 0
  4 p11543 p7870 p11544 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p11548 :=
p11546 p11544 1118918670 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p11547 (Eq.refl true))

noncomputable def p11549 :=
@BSN.binarySplit_of_base4 (BSN.cosOddP 7307572493) (BSN.cosOddQ 4294967296) 0 4
  p11545 p7873 p11544 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p11550 :=
p11542
  (BSN.cos_neg_of_bound 7307572493 4294967296 true 1118918670 8589934592
    1 3300000000
    (p11548 (p11549 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p11551 :=
p11496
  (p11499
    (@Enclosure.Real.IsNear.neg p11498 false 60569408943 17179869184
      3285 17179869184 (p11525 (Eq.refl true))))
  (@p11526 1118918670 8589934592 2066479869184
    56693568307200000000 559459335 4294967296 8072186989
    221459251200000000 (p11550 (Eq.refl true)) (Eq.refl true))

noncomputable def p11552 :=
@p11489 p11464
  (@p11492 false 33886121248593832905 73786976294838206464
    1520027127499788513 p11485
    (BSN.correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
        (Enclosure.sfrac false 12 1))
      (p11493 (Eq.refl true) (Eq.refl true)
        (p11275 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p11551 (Eq.refl true)))

noncomputable def p11553 :=
nat_lit
  512839428090668259486581439336902201592522609824320807891763733613544520998836478146502006989527552516453751081844392426809442790177146676504559952208625

noncomputable def p11554 :=
@Enclosure.Real.IsNear.mulLit_tf
  (Zeta.RiemannSiegel.correctionLinear
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
      (Enclosure.sfrac false 12 1)))
  (@Inv.inv.{0} Real Real.instInv p11272) p11553 p7279

noncomputable def p11555 :=
nat_lit
  25325179260445081624869721414609848428781513654731460447078133567185765907993179984637985422053919988494832327675124813131050890188269095007955704707653165042417047642028987089880806057297028423798487736779

noncomputable def p11556 :=
nat_lit
  519611609492772484596320794496497772825764802823389830106508691709166983265051708760681795581065056805425980411979644097894536252175155200000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p11557 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
      (Enclosure.sfrac false 12 1)))
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 96 1)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi)))

noncomputable def p11558 :=
@Enclosure.Real.IsNear.of_eq
  (Zeta.RiemannSiegel.correctionLinear
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
      (Enclosure.sfrac false 12 1)))
  (@Neg.neg.{0} Real Real.instNeg p11557) true p11553

noncomputable def p11559 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
      (Enclosure.sfrac false 12 1)))
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 96 1)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi)))

noncomputable def p11560 :=
nat_lit
  110482264636780270800958833337200999988949953699268831329846816669820369164118769964336114794416850067962696933263617610952823482924498035371575

noncomputable def p11561 :=
nat_lit
  5455635313709225850459928436263096652898326687972683666584441980371389757791037686802051442336312608472019193694709207065068452575678659413913356619668478777297971052037371295531413055984909634669

noncomputable def p11562 :=
nat_lit
  118146001453345089566100976866550302662691320352539567035480261372223818231089287283039492554295306218915807315165612657868800000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p11563 :=
@p11559 p11560 p7287 p11561
  p11562 4641825815 4398046511104 1 4398046511104
  p11553 p7279 p11555

noncomputable def p11564 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p11565 :=
p11564
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p11566 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p11565
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p11567 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p11566
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p11491 (Enclosure.sfrac false 1 16)))))

noncomputable def p11568 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (Enclosure.sfrac false 3 1)
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p11569 :=
p11567
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p11568
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 4 1) Real.pi))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p11491 (Enclosure.sfrac false 1 16)))))

noncomputable def p11570 :=
@Neg.neg.{0} Real Real.instNeg
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
          (Enclosure.sfrac false 12 1)))))

noncomputable def p11571 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11569
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 3 1) p11570)
    (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
        (Enclosure.sfrac false 12 1))))

noncomputable def p11572 :=
@Neg.neg.{0} Real Real.instNeg
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 4 1)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
          (Enclosure.sfrac false 12 1)))))

noncomputable def p11573 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11571
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 3 1) p11572)
    (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
        (Enclosure.sfrac false 12 1))))

noncomputable def p11574 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 8 1)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi) Real.pi))
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
        (Enclosure.sfrac false 12 1))))

noncomputable def p11575 :=
@Enclosure.Real.IsNear.of_eq
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
      (Enclosure.sfrac false 12 1)))
  (p11490
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11573
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p11574
        (Zeta.RiemannSiegel.correction
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
            (Enclosure.sfrac false 12 1))))))

noncomputable def p11576 :=
@p11494
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11573
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p11574
      (Zeta.RiemannSiegel.correction
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
          (Enclosure.sfrac false 12 1)))))
  15505768149147

noncomputable def p11577 :=
nat_lit
  7125236465170420951105811704561973433927639182352220812252584920965158640122066463657283401849170098015430407868621442586496920725

noncomputable def p11578 :=
nat_lit
  1055492733695484855451020202223264275770442549824167843655926996194304858154805300739423587317414255495183579305147558995859791656444031930534245039082830920683366345835886670079132101

noncomputable def p11579 :=
nat_lit
  80589871768105528803585668947482851760486019215390729438340891673913450789147614579887539926604840424430999961600000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p11580 :=
@p11576 4398046511104 3285 4398046511104 p11577
  p7305 p11578 p11579 p11560
  p7287 p11561 p11562

noncomputable def p11581 :=
@p11497 (@Neg.neg.{0} Real Real.instNeg p11498) true 15505768149147
  4398046511104 3285 4398046511104
  (BSN.inv_eq_neg_inv_neg
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
          (Enclosure.sfrac false 12 1)))))

noncomputable def p11582 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
      (Enclosure.sfrac false 12 1)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 9730241927191)
    (@Nat.cast.{0} Real Real.instNatCast 2199023255552))
  false

noncomputable def p11583 :=
nat_lit 2738819619845210152287368675

noncomputable def p11584 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
      (Enclosure.sfrac false 12 1)))
  false p11583

noncomputable def p11585 :=
nat_lit 1106455696792823407049145567

noncomputable def p11586 :=
@Enclosure.Real.IsNear.subLit_ff_p p11272 (Enclosure.sfrac false 12 1)
  55873790333633 4398046511104 41 4398046511104 12 1
  0

noncomputable def p11587 :=
@p11474
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 101409000 100000)
    (@Inv.inv.{0} Real Real.instInv
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)))
  false 70983343135747119

noncomputable def p11588 :=
@p11587 439804651110400 101409 439804651110400
  (BSN.t_div_two_pi_mk
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
      true 5)
    101409000 100000
    (Enclosure.sfrac_ofScientific_eq 101409000 5 100000 (Eq.refl true)))

noncomputable def p11589 :=
@p11477 1 699970842191 4398046511104 1 4398046511104
  70983343135747119 439804651110400 101409 439804651110400
  (Enclosure.Real.IsNear.const false 101409000 100000) d145

noncomputable def p11590 :=
@p11473 70983343135747119 439804651110400 101409
  439804651110400 27936895166796 27936895166837 2199023255552
  (p11588 (p11589 (Eq.refl true))) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p11591 :=
@Enclosure.Real.IsNear.recentre' p11272 false 55873790333633 4398046511104
  41 4398046511104 55873790333633 4398046511104 41
  4398046511104
  (p11590 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p11592 :=
@p11507 500000000000000 3097232200385 4398046511104 41
  4398046511104 p11583 p504 p11585
  p2694 d144
  (@p11586 1 3097232200385 3097232200385 4398046511104
    41 4398046511104 (p11591 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p11593 :=
@p11582 9730241927191 2199023255552 259 4398046511104
  true 1247459198911 4398046511104 1 844800000000
  (@p11584 p504 p11585 p2694
    9730241927191 2199023255552 259 4398046511104
    (p11592 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div 9730241927191 2199023255552)

noncomputable def p11594 :=
nat_lit 406665192111784960954552287232

noncomputable def p11595 :=
BSN.cos_reduce2
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 9730241927191)
    (@Nat.cast.{0} Real Real.instNatCast 2199023255552))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast p11594)
    (@Nat.cast.{0} Real Real.instNatCast p7323))
  226375608064910080 72057594037927936 false

noncomputable def p11596 :=
BSN.sin_reduce_arg_pos_rat_q2 9730241927191 2199023255552 226375608064910080
  72057594037927936 0 p11594 p7323 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p11597 :=
nat_lit
  4443599287338642731165053142772467210827258419091830333311233103332873042378798233137854961371913306148797771570194551928026090573191667571790363039366402009926305223814506269098954675180872029561080882048927848771401890815439634795777056333598956403904671210595680256

noncomputable def p11598 :=
nat_lit
  101436706871252998565901240869863160179691389996607311780923462642890975936722302001690481441358992997611433289668888057494166862662555161979373790615480611171263551769279803652708139128453816567397675916629265840460354002015069030330301042646410109256728576

noncomputable def p11599 :=
nat_lit
  45276010609655699929885136297486443690033884361067190285570016478441860871006452241988212766118926311633975389783101145275290772553771224047509182490149427426359998492229850826719764129899869764690471108132905832336133617788947959310145205405128650630037482557644210176

noncomputable def p11600 :=
BSN.cos_dyadic_bound_f 11558119925660576 9007199254740992 5 4
  4398046511104 1691250000001 p11597 p2708
  p11598 p11599 p2711

noncomputable def p11601 :=
@BSN.binarySplit_of_base4 (BSN.cosEvenP 11558119925660576) (BSN.cosEvenQ 9007199254740992)
  0 4 p11597 p2708 p11598
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p11602 :=
p11600 p11598 1247459198911 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p11601 (Eq.refl true))

noncomputable def p11603 :=
@BSN.binarySplit_of_base4 (BSN.cosOddP 11558119925660576) (BSN.cosOddQ 9007199254740992) 0
  4 p11599 p2711 p11598 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p11604 :=
@BSN.cos_arg_round false 1247459198911 4398046511104 p11594
  p7323 11558119925660576 9007199254740992 1691250000001
  1689600000000
  (p11602 (p11603 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p11605 :=
p11595 1247459198911 4398046511104 0 1000000000000000
  1689600000000 844800000000 p11596 BSN.pi_near_15 p11604
  (Eq.refl true) (Eq.refl true)

noncomputable def p11606 :=
@p11501 1247459198911 4398046511104 3405780739
  56693568307200000000
  (@p11502 1247459198911 4398046511104 223201246511104
    p2689 1247459198911 4398046511104 3405780739
    56693568307200000000
    (p11593 (p11605 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p11607 :=
@p11500 1247459198911 4398046511104 3405780739
  56693568307200000000 7752884072931 7752884076216 2199023255552
  p11606 (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p11608 :=
@Enclosure.Real.IsNear.recentre' p11498 false 15505768149147 4398046511104
  3285 4398046511104 15505768149147 4398046511104 3285
  4398046511104
  (p11607 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p11609 :=
nat_lit
  310002904993514058174299995834130121146884117117307982690287400700965177475065089963005437240973645880039291672433443223181184920725

noncomputable def p11610 :=
@Enclosure.Real.IsNear.subLit_tt_n p11573
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p11574
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
        (Enclosure.sfrac false 12 1))))
  p11609 p7305

noncomputable def p11611 :=
nat_lit
  1043453440109410493921509766811414091671937865729148345946488944868276515749992757128140183779428243466946324137457910245147196288357993731350985350693187410248020487275886670079132101

noncomputable def p11612 :=
nat_lit 6476165951340468085397645418212678633229144711968774784405281105478680405471109375

noncomputable def p11613 :=
nat_lit
  4647560224165736275400325723444242022788188833695682775599192494597764109417511611082326551731271767272440443404370601

noncomputable def p11614 :=
nat_lit
  31110320536854051734492386107724907984829849959634869291434639360000000000000000000000000000000000000000000000000000000000000

noncomputable def p11615 :=
nat_lit
  422423560505340309680868634597709211113872261871891353468888552758687647938112259512954181535996433448729635654859188375876338469758614487125584991420909030611069374852659037337425117396584281514082296869683200

noncomputable def p11616 :=
@p11610 p11611 p11579 p11612
  p7342 p11613 p11614 p11615
  p11577 p7305 p11578 p11579

noncomputable def p11617 :=
@Enclosure.Real.IsNear.subLit_tf p11571
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 3 1) p11572)
    (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
        (Enclosure.sfrac false 12 1))))

noncomputable def p11618 :=
nat_lit
  236954622524221553457109026202515089386605290463073700753101678314620116169153584681978462935480879131020761850303565439873306520725

noncomputable def p11619 :=
nat_lit
  1001839697301300734408236995937078894983741253929041379777308888864635234477269065171980416049400556268633626126984554137889906296411505267965778330707817430091762702207970177279132101

noncomputable def p11620 :=
nat_lit 30212061519447983533160815887329132129843989592188312495422725881416391603151570251452128160351769498340625

noncomputable def p11621 :=
nat_lit
  1335159515796805075984583314138908098643631264046553724149289198756143244999876782957792080097398740477703066261243601547369787501269265158891491356673

noncomputable def p11622 :=
nat_lit
  2585692295552445393393803797982103664741043502778397702786162317362481603608132511072256000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p11623 :=
nat_lit
  355495616777763060578230314895420178119799340190801187084488838731515871049644197609135885818908720088762333917716984632138918632576530999693405385209974633714269094787159450436719211136483157059372530134690899800594658413168873911091200

noncomputable def p11624 :=
@p11617 p11618 p7305 p11619
  p11579 p11620 p7351 p11621
  p11622 p11623 p11609 p7305

noncomputable def p11625 :=
@Enclosure.Real.IsNear.subLit_tf p11569
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 3 1) p11570)
    (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
        (Enclosure.sfrac false 12 1))))

noncomputable def p11626 :=
nat_lit 135483872299315526956266049074138905818860310137557769668307897389400462513931691432746739025

noncomputable def p11627 :=
nat_lit
  227512127500920343334706312340079179406885609232231655463693538586354665543938079094680918960943271063675126849585566086017

noncomputable def p11628 :=
nat_lit
  11941059202598232653055757829020940497368467168644183166569063350816041494118400000000000000000000000000000000000000000000000000000

noncomputable def p11629 :=
nat_lit
  225428929337815239238955352904617597478035474269445228092536301559921865614518926129089005251973798713465920451874846491563144703125

noncomputable def p11630 :=
nat_lit
  333434741456545545993865851984234171761083136928345936726061512311854498419848064893512129590270204460474224971965184883717038768241345172952168326291814798361254234069323392426377367

noncomputable def p11631 :=
nat_lit
  26863290589368509601195222982494283920162006405130243146113630557971150263049204859962513308868280141476999987200000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p11632 :=
nat_lit
  7722961453449556161569312219309713040271272753982323332136820953438965930424829158921791228505530728633440973584771810959479070135101198684180889202473872355701204276335779886035901737535915736953687740009478723114473881600

noncomputable def p11633 :=
@p11625 p11626 p7956 p11627
  p11628 p11629 p7305 p11630
  p11631 p11632 p11618 p7305

noncomputable def p11634 :=
@Enclosure.Real.IsNear.subLit_tt_n
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p11566
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p11491 (Enclosure.sfrac false 1 16)))))

noncomputable def p11635 :=
@p11634
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p11568
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 4 1) Real.pi))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p11491 (Enclosure.sfrac false 1 16)))))

noncomputable def p11636 :=
nat_lit 546241748708062237377049382539453650813834689439021556313571453780053883254864390416742540625

noncomputable def p11637 :=
nat_lit
  56145352489530747180155510103101902380833032851650702405272301901950224840650069458862687075193668470399222849585566086017

noncomputable def p11638 :=
nat_lit 603554454092801399064244424247465874250769400190084925

noncomputable def p11639 :=
nat_lit 171896043472659126870366633527188253101565248353621150843421707455112847

noncomputable def p11640 :=
nat_lit 11977939315617033913910786181598241043251200000000000000000000000000000000000000

noncomputable def p11641 :=
nat_lit
  6488388442435767675764059185707508473231046434405153983897062871052792690189234302194405481360762991783453405048766945056215462190765468496691200

noncomputable def p11642 :=
@p11635 p11636 p7956 p11637
  p11628 p11638 p5762 p11639
  p11640 p11641 p11626 p7956

noncomputable def p11643 :=
nat_lit 501073137346451451456687610743275505137789699419329926451185602969265589802930875

noncomputable def p11644 :=
@Enclosure.Real.IsNear.mulLit_ft p11566
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p11491 (Enclosure.sfrac false 1 16))))
  p11643

noncomputable def p11645 :=
nat_lit 1950213148339865300306891206669350421908085078384172892692479470008557369914295079581234273932586759937

noncomputable def p11646 :=
@p11644 p2761 p11645 p5163
  1090143749475 1099511627776 8072186989 56693568307200000000
  p11636 p7956 p11637 p11628

noncomputable def p11647 :=
@Enclosure.Real.IsNear.mulLit_ff p11565
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p11648 :=
nat_lit 630861581708321182915421284357494629559962303466129225

noncomputable def p11649 :=
nat_lit 53638140776330504110812752004927847317700498037168869541087284339

noncomputable def p11650 :=
nat_lit 794267953343404874725881315

noncomputable def p11651 :=
nat_lit 1106436807326891928468290783

noncomputable def p11652 :=
@p11647 p11648 p2767 p11649
  p5168 p11650 p976 p11651
  p5171 p11643 p2761 p11645

noncomputable def p11653 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p11654 :=
@p11653
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p11655 :=
@p11654 p11650 p976 p11651
  p5171 p11650 p976 p11651
  p5171 p11648 p2767 p11649

noncomputable def p11656 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
        (Enclosure.sfrac false 12 1)))
    (Enclosure.sfrac false 1 1))
  884279719003555

noncomputable def p11657 :=
@p11656 140737488355328 1 500000000000000 898208944833
  2199023255552 41 2199023255552 p11650 p976
  p11651 p5171

noncomputable def p11658 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 2 1)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
      (Enclosure.sfrac false 12 1)))
  (Enclosure.sfrac false 1 1) 3097232200385 2199023255552

noncomputable def p11659 :=
@p11658 41 2199023255552 1 1 0 1
  898208944833 898208944833 2199023255552 41 2199023255552

noncomputable def p11660 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 2 1)
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
    (Enclosure.sfrac false 12 1))
  2 1 0 1

noncomputable def p11661 :=
@p11660 3097232200385 4398046511104 41 4398046511104
  3097232200385 2199023255552 41 2199023255552
  (Enclosure.Real.IsNear.const false 2 1)
  (@p11586 1 3097232200385 3097232200385 4398046511104
    41 4398046511104 (p11591 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p11662 :=
@p11655 p5168
  (p11657 d144
    (p11659 (p11661 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (p11657 d144
    (p11659 (p11661 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))

noncomputable def p11663 :=
@p11652 p5163 (p11662 (Eq.refl true))
  (p11657 d144
    (p11659 (p11661 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p11664 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p11491 (Enclosure.sfrac false 1 16))))
  true

noncomputable def p11665 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p11491 (Enclosure.sfrac false 1 16)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Neg.neg.{0} Real Real.instNeg (@Nat.cast.{0} Real Real.instNatCast 3741477125751))
    (@Nat.cast.{0} Real Real.instNatCast 2199023255552))
  true

noncomputable def p11666 :=
nat_lit 4631724340037587363908503731740981783005

noncomputable def p11667 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p11491 (Enclosure.sfrac false 1 16)))
  true p11666

noncomputable def p11668 :=
nat_lit 11719907220629558525247260997503223538677

noncomputable def p11669 :=
nat_lit 5237849789495134636132991

noncomputable def p11670 :=
nat_lit 4028923969880505461426815

noncomputable def p11671 :=
@p11532 (Enclosure.sfrac false 1 16) p11670
  p2793 434292947388515 p2793 1 16 0

noncomputable def p11672 :=
nat_lit 83805596631922154178127856

noncomputable def p11673 :=
nat_lit 9592847303101708794148225

noncomputable def p11674 :=
@Enclosure.Real.IsNear.subLit_ff_n
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
      (Enclosure.sfrac false 12 1))
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
      (Enclosure.sfrac false 12 1)))
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
    (Enclosure.sfrac false 12 1))
  p11673

noncomputable def p11675 :=
nat_lit 17719395009236234224412221360580853760

noncomputable def p11676 :=
@p11674 p2793 253973040433251 p2793
  3097232200385 4398046511104 41 4398046511104 p11675
  p11670 p2793 434292947388515

noncomputable def p11677 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
    (Enclosure.sfrac false 12 1))
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
    (Enclosure.sfrac false 12 1))
  3097232200385 4398046511104 41

noncomputable def p11678 :=
@p11677 4398046511104 3097232200385 4398046511104 41
  4398046511104 p11673 p2793 253973040433251
  p2793
  (@p11586 1 3097232200385 3097232200385 4398046511104
    41 4398046511104 (p11591 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p11679 :=
p11678
  (@p11586 1 3097232200385 3097232200385 4398046511104
    41 4398046511104 (p11591 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p11680 :=
@p11676 p2793 (p11679 (Eq.refl true))
  (@p11586 1 3097232200385 3097232200385 4398046511104
    41 4398046511104 (p11591 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p11681 :=
@p11531 500000000000000 p11669 p2793
  434292947388515 p2793 p11666 p2789
  p11668 p2791 d144
  (@p11671 1 p11672 p11669 p2793
    434292947388515 p2793
    (p11680 (Eq.refl true) (Eq.refl true))
    (Enclosure.Real.IsNear.const false 1 16) (Eq.refl true)
    (Eq.refl true))

noncomputable def p11682 :=
@p11665 3741477125751 2199023255552 621 4398046511104
  true 2180287498950 2199023255552 1 844800000000
  (@p11667 p2789 p11668 p2791
    3741477125751 2199023255552 621 4398046511104
    (p11681 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_true_div 3741477125751 2199023255552)

noncomputable def p11683 :=
nat_lit
  7447662048897647271354305131671021032867880588004287143769343912069869846197833188826787171936145560441730028874789141251177270805850453466370496054945031225959325149279510257099703138160681651452583809220449921

noncomputable def p11684 :=
nat_lit
  1474651886595243414482520640184186260211460828477212914365664193869542524690028125587790014194568210893310481110069908187945214489702040628897251891507046114325157164062578813754169306912917466826512001

noncomputable def p11685 :=
nat_lit
  60541577351703262744757745415429291563696737275455278383467380100691271189934658644046745375614319845654678681464861476721405059525080766738323377186265430085608949389613106436620467183867505015049157382921361025

noncomputable def p11686 :=
BSN.sin_dyadic_bound_f 3741477125751 2199023255552 5 4 2199023255552
  844800000000 p11683 p3441 p11684
  p11685 p3444

noncomputable def p11687 :=
@BSN.binarySplit_of_base4 (BSN.sinEvenP 3741477125751) (BSN.sinEvenQ 2199023255552) 0
  4 p11683 p3441 p11684 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p11688 :=
p11686 p11684 2180287498950 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p11687 (Eq.refl true))

noncomputable def p11689 :=
@BSN.binarySplit_of_base4 (BSN.sinOddP 3741477125751) (BSN.sinOddQ 2199023255552) 0
  4 p11685 p3444 p11684 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p11690 :=
p11682
  (BSN.sin_neg_of_bound 3741477125751 2199023255552 false 2180287498950
    2199023255552 1 844800000000
    (p11688 (p11689 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p11691 :=
p11646 p11663
  (@p11664 2180287498950 2199023255552 529018846511104
    p2689 1090143749475 1099511627776 8072186989
    56693568307200000000 (p11690 (Eq.refl true))
    (Eq.refl true))

noncomputable def p11692 :=
nat_lit 2107065127788104387099905006755602979224475

noncomputable def p11693 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p11568
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 4 1) Real.pi))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p11491 (Enclosure.sfrac false 1 16))))
  p11692

noncomputable def p11694 :=
nat_lit 89575785991331412184681862020673732628261128861193483

noncomputable def p11695 :=
@p11693 p2820 p11694 p5216
  286443188743 2199023255552 8072186989 56693568307200000000
  p11638 p5762 p11639 p11640

noncomputable def p11696 :=
nat_lit 2382803860030214624177643945

noncomputable def p11697 :=
nat_lit 3319310421980675785404872349

noncomputable def p11698 :=
@Enclosure.Real.IsNear.mulLit_ff p11568
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 4 1) Real.pi)
  p11696 p976 p11697 p5171

noncomputable def p11699 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 3 1)
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p11700 :=
@p11699 3 1 0 1 p11650
  p976 p11651 p5171 p11696
  p976 p11697

noncomputable def p11701 :=
@p11700 p5171 (Enclosure.Real.IsNear.const false 3 1)
  (p11657 d144
    (p11659 (p11661 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p11702 :=
@p11698 884279719003555 70368744177664 1 250000000000000
  p11692 p2820 p11694 p5216
  p11701 d146 (Eq.refl true)

noncomputable def p11703 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p11491 (Enclosure.sfrac false 1 16)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Neg.neg.{0} Real Real.instNeg (@Nat.cast.{0} Real Real.instNatCast 3741477125751))
    (@Nat.cast.{0} Real Real.instNatCast 2199023255552))
  true

noncomputable def p11704 :=
@p11703 3741477125751 2199023255552 621 4398046511104
  true 286443188743 2199023255552 1 844800000000
  (@p11667 p2789 p11668 p2791
    3741477125751 2199023255552 621 4398046511104
    (p11681 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_true_div 3741477125751 2199023255552)

noncomputable def p11705 :=
nat_lit
  2195336406375908520374330220027522888921474216191211816830548906190338787645590511476644145006680680214446391759729724726674458678545431242463367606086929553822518569537888123697521774574217874635134725997041281

noncomputable def p11706 :=
nat_lit
  22318270442239576217424659010473981186789551013710998844287507263602517658385754443941953054980160862580990283147738379287499278898346159276205238849386754958669272401206097238423096484879308325315150153749468801

noncomputable def p11707 :=
BSN.cos_dyadic_bound_t 3741477125751 2199023255552 5 4 2199023255552
  844800000000 p11705 p3467 p11684
  p11706 p3469

noncomputable def p11708 :=
@BSN.binarySplit_of_base4 (BSN.cosEvenP 3741477125751) (BSN.cosEvenQ 2199023255552) 0
  4 p11705 p3467 p11684 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p11709 :=
p11707 p11684 286443188743 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p11708 (Eq.refl true))

noncomputable def p11710 :=
@BSN.binarySplit_of_base4 (BSN.cosOddP 3741477125751) (BSN.cosOddQ 2199023255552) 0
  4 p11706 p3469 p11684 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p11711 :=
p11704
  (BSN.cos_neg_of_bound 3741477125751 2199023255552 true 286443188743
    2199023255552 1 844800000000
    (p11709 (p11710 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p11712 :=
p11695 p11702
  (@p11526 286443188743 2199023255552 529018846511104
    p2689 286443188743 2199023255552 8072186989
    56693568307200000000 (p11711 (Eq.refl true))
    (Eq.refl true))

noncomputable def p11713 :=
nat_lit 5594072736814704966473645625

noncomputable def p11714 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 3 1) p11570)
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
      (Enclosure.sfrac false 12 1)))
  p11713

noncomputable def p11715 :=
nat_lit 91909122843018485090821355799126613

noncomputable def p11716 :=
nat_lit 40297818770618217100793483673571745763165141739123955097469559129309728212555502451359862299868701892925

noncomputable def p11717 :=
nat_lit
  454361687289722978009896005956421459459972351414974659009768417212110377801880635777705180815152461892490296415994466920625098890776045793

noncomputable def p11718 :=
nat_lit
  661937227661426020708813772283418538173707136711269811913257553244795290523681922834497536000000000000000000000000000000000000000000000000000000

noncomputable def p11719 :=
@p11714 p976 p11715 p2846
  p11716 p7449 p11717 p11718
  p11629 p7305 p11630 p11631

noncomputable def p11720 :=
nat_lit 1864690912271568322157881875

noncomputable def p11721 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 3 1) p11570
  3 1 0 1 p11720 p976

noncomputable def p11722 :=
@Enclosure.Real.IsNear.neg
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
          (Enclosure.sfrac false 12 1)))))

noncomputable def p11723 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
        (Enclosure.sfrac false 12 1))))
  884279719003555

noncomputable def p11724 :=
@p11723 140737488355328 1 500000000000000 2108711612625
  2199023255552 3405780739 56693568307200000000 p11720
  p976 p11715 p2854

noncomputable def p11725 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
        (Enclosure.sfrac false 12 1))))
  true

noncomputable def p11726 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
      (Enclosure.sfrac false 12 1)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 9730241927191)
    (@Nat.cast.{0} Real Real.instNatCast 2199023255552))
  false

noncomputable def p11727 :=
@p11726 9730241927191 2199023255552 259 4398046511104
  true 4217423225250 4398046511104 1 844800000000
  (@p11584 p504 p11585 p2694
    9730241927191 2199023255552 259 4398046511104
    (p11592 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div 9730241927191 2199023255552)

noncomputable def p11728 :=
BSN.sin_reduce2
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 9730241927191)
    (@Nat.cast.{0} Real Real.instNatCast 2199023255552))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast p11594)
    (@Nat.cast.{0} Real Real.instNatCast p7323))
  226375608064910080 72057594037927936 false

noncomputable def p11729 :=
nat_lit
  15097414557685729518323897179467416394481960225073462222245544216136212237621167858342827479213458927723426696397120048805573940125126506972118243972170851843703656820589086037413275704292149515943448058430234926181391133050415965233619132311260390189182666882831876096

noncomputable def p11730 :=
nat_lit
  122867996877473330186938886146970122566860206914999403916026040710796925553000776826325394675272156011915682418541503885933971849029421133833364522578136419896519710834042778094129436041828758928602156264373867419147733015140965362718753918486632785810983296819129221120

noncomputable def p11731 :=
BSN.sin_dyadic_bound_f 11558119925660576 9007199254740992 5 4
  4398046511104 1691250000001 p11729 p10241
  p11598 p11730 p10243

noncomputable def p11732 :=
@BSN.binarySplit_of_base4 (BSN.sinEvenP 11558119925660576) (BSN.sinEvenQ 9007199254740992)
  0 4 p11729 p10241 p11598
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p11733 :=
p11731 p11598 4217423225250 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p11732 (Eq.refl true))

noncomputable def p11734 :=
@BSN.binarySplit_of_base4 (BSN.sinOddP 11558119925660576) (BSN.sinOddQ 9007199254740992) 0
  4 p11730 p10243 p11598 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p11735 :=
@BSN.sin_arg_round false 4217423225250 4398046511104 p11594
  p7323 11558119925660576 9007199254740992 1691250000001
  1689600000000
  (p11733 (p11734 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p11736 :=
p11728 4217423225250 4398046511104 0 1000000000000000
  1689600000000 844800000000 p11596 BSN.pi_near_15 p11735
  (Eq.refl true) (Eq.refl true)

noncomputable def p11737 :=
p11724 d144
  (@p11725 4217423225250 4398046511104 223201246511104
    p2689 2108711612625 2199023255552 3405780739
    56693568307200000000
    (p11727 (p11736 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p11738 :=
@Neg.neg.{0} Real Real.instNeg
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p11565
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p11491 (Enclosure.sfrac false 1 16)))))

noncomputable def p11739 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11738
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 4 1) Real.pi)
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p11491 (Enclosure.sfrac false 1 16)))))

noncomputable def p11740 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11739
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) p11570)
    (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
        (Enclosure.sfrac false 12 1))))

noncomputable def p11741 :=
@Enclosure.Real.IsNear.of_eq
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
      (Enclosure.sfrac false 12 1)))
  (p11490
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11740
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p11572
        (Zeta.RiemannSiegel.correction
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
            (Enclosure.sfrac false 12 1))))))

noncomputable def p11742 :=
@p11494
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11740
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p11572
      (Zeta.RiemannSiegel.correction
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
          (Enclosure.sfrac false 12 1)))))
  15505768149147

noncomputable def p11743 :=
nat_lit 2598892127303933155055187553209598374270347203171392786611139750357290775021053792968832775

noncomputable def p11744 :=
nat_lit
  29262071831350176279564912484983442760487102405244430486679296421936372637124314065336050390233405920713137598402358285929299

noncomputable def p11745 :=
nat_lit
  150507100366081890731223614303284770852248388271452725328630902650910522998784000000000000000000000000000000000000000000000000000000

noncomputable def p11746 :=
@p11742 4398046511104 3285 4398046511104 p11743
  p7478 p11744 p11745 p11716
  p7449 p11717 p11718

noncomputable def p11747 :=
nat_lit 7876423404558409863202810460386654387631937709280617130667440149881288582734285866101836025

noncomputable def p11748 :=
@Enclosure.Real.IsNear.subLit_ff_n p11740
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p11572
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
        (Enclosure.sfrac false 12 1))))
  p11747 p7478

noncomputable def p11749 :=
nat_lit
  28088169093571347562119927697838973676567747677632491477460101878639774872170433497108780974342085532348770365692931085929299

noncomputable def p11750 :=
nat_lit 4332488959166068894863381712499512237029837419967790611272744461275

noncomputable def p11751 :=
nat_lit 112992533610306066704095908533417021946866029745707146105923668600223139168373732050451986581

noncomputable def p11752 :=
nat_lit 14486871909747855614168749241030266501395893264391864320000000000000000000000000000000000000000000000

noncomputable def p11753 :=
nat_lit
  2189562285805990904251240137516517075202996609302457854268136772517117897351562158098306914712824991604110422513685776420550281118255078437259612729324339200

noncomputable def p11754 :=
@p11748 p11749 p11745 p11750
  p7486 p11751 p11752 p11753
  p11743 p7478 p11744 p11745

noncomputable def p11755 :=
@Enclosure.Real.IsNear.subLit_ff_p p11739
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) p11570)
    (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
        (Enclosure.sfrac false 12 1))))

noncomputable def p11756 :=
nat_lit 2804941861771006331211356380895876835449873409334799372502253778175

noncomputable def p11757 :=
nat_lit 2364568031004154781822706897616768547941283976546271110261981266606805064817436999941

noncomputable def p11758 :=
nat_lit 19251309709144771904901131120050404938596377553441070139233637135024679695819562465950234375

noncomputable def p11759 :=
nat_lit
  27665941226463356872613693210626273082234668512239787829060893313374073218236163682444609808548045632907700285692931085929299

noncomputable def p11760 :=
nat_lit
  1658968397771810917208185051421010480358289130144217979831061229598083631986027318598823021985067713100516521532731126448736171168450161265500200484261068800

noncomputable def p11761 :=
@p11755 p11756 p5882 p11757
  p5884 p11758 p7478 p11759
  p11745 p11760 p11747 p7478

noncomputable def p11762 :=
@Enclosure.Real.IsNear.subLit_ft p11738
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 4 1) Real.pi)
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p11491 (Enclosure.sfrac false 1 16)))))

noncomputable def p11763 :=
nat_lit 180706003119984160971507045960573307661653149127713496704303314175

noncomputable def p11764 :=
nat_lit 2569403917281963654147689683567322515538551081889893163721306007761023194452310999823

noncomputable def p11765 :=
nat_lit 963992008459234858554383625

noncomputable def p11766 :=
nat_lit 217837129645895114838925758213970363

noncomputable def p11767 :=
nat_lit 217021864909625454144831532643496474609826522101773498159208618279247746228430786656416563200

noncomputable def p11768 :=
@p11762 p11763 p5882 p11764
  p5892 p11765 p3406 p11766
  p2908 p11767 p11756 p5882

noncomputable def p11769 :=
@Enclosure.Real.IsNear.neg
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p11565
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p11491 (Enclosure.sfrac false 1 16)))))

noncomputable def p11770 :=
@Enclosure.Real.IsNear.mulLit_ft p11565
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p11491 (Enclosure.sfrac false 1 16))))
  p11648

noncomputable def p11771 :=
@p11770 p2767 p11649 p5168
  286443188743 2199023255552 8072186989 56693568307200000000
  p11763 p5882 p11764 p5892

noncomputable def p11772 :=
p11771 (p11662 (Eq.refl true))
  (@p11526 286443188743 2199023255552 529018846511104
    p2689 286443188743 2199023255552 8072186989
    56693568307200000000 (p11711 (Eq.refl true))
    (Eq.refl true))

noncomputable def p11773 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 4 1) Real.pi)
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p11491 (Enclosure.sfrac false 1 16))))
  884279719003555

noncomputable def p11774 :=
@p11773 70368744177664 1 250000000000000 1090143749475
  1099511627776 8072186989 56693568307200000000 p11765
  p3406 p11766 p2908

noncomputable def p11775 :=
p11774 d146
  (@p11664 2180287498950 2199023255552 529018846511104
    p2689 1090143749475 1099511627776 8072186989
    56693568307200000000 (p11690 (Eq.refl true))
    (Eq.refl true))

noncomputable def p11776 :=
@p11761 p11749 p11745
  (@p11768 p11757 p5884
    (@p11769 true p11763 p5882 p11764
      p5892 (p11772 (Eq.refl true)))
    (p11775 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p11777 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 2 1) p11570)
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
      (Enclosure.sfrac false 12 1)))
  p11720

noncomputable def p11778 :=
nat_lit 10324129099601181242621444492129711269731691643461864896418504125

noncomputable def p11779 :=
nat_lit 112780691943609534358519459102179372692540338432119608977791974558134039347519663

noncomputable def p11780 :=
nat_lit 7417278417790902074454399611407496448714697351368634531840000000000000000000000000000000

noncomputable def p11781 :=
@p11777 p982 p11715 p2908
  p11778 p5277 p11779 p11780
  p11758 p7478 p11759 p11745

noncomputable def p11782 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 2 1) p11570
  2 1 0 1 p11720 p976

noncomputable def p11783 :=
@Neg.neg.{0} Real Real.instNeg
  (p11564
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p11491 (Enclosure.sfrac false 1 16)))))

noncomputable def p11784 :=
@Enclosure.Real.IsNear.of_eq
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
      (Enclosure.sfrac false 12 1)))
  (p11490
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11783
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p11570
        (Zeta.RiemannSiegel.correction
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
            (Enclosure.sfrac false 12 1))))))

noncomputable def p11785 :=
@p11494
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11783
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p11570
      (Zeta.RiemannSiegel.correction
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
          (Enclosure.sfrac false 12 1)))))
  15505768149147

noncomputable def p11786 :=
nat_lit 665825065891310262099251893283363271151606927242375

noncomputable def p11787 :=
nat_lit 21581960870768819037233567493139976237177355752684763265328525483627

noncomputable def p11788 :=
nat_lit 5059481566916635125235916083107097016669306880000000000000000000000000000000

noncomputable def p11789 :=
@p11785 4398046511104 3285 4398046511104 p11786
  p7523 p11787 p11788 p11778
  p5277 p11779 p11780

noncomputable def p11790 :=
nat_lit 865866244745613752396664919557943559625

noncomputable def p11791 :=
@Enclosure.Real.IsNear.subLit_ff_n p11783
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p11570
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
        (Enclosure.sfrac false 12 1))))
  p11790 p8122

noncomputable def p11792 :=
nat_lit 128928115932771877853197494914085261135241040881

noncomputable def p11793 :=
nat_lit 8282065099463647733569879628777688243906962624394375

noncomputable def p11794 :=
nat_lit 6381831962772583779066137267508479040439614432192276514371375161209

noncomputable def p11795 :=
nat_lit 1686493855638878375078638694369032338889768960000000000000000000000000000000

noncomputable def p11796 :=
nat_lit 226568529376784867944556987435871649652961167712195313340685497284488993767405175963648000

noncomputable def p11797 :=
@p11791 p11792 p5920 p11793
  p7523 p11794 p11795 p11796
  p11786 p7523 p11787 p11788

noncomputable def p11798 :=
@Enclosure.Real.IsNear.neg
  (p11564
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p11491 (Enclosure.sfrac false 1 16)))))

noncomputable def p11799 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p11800 :=
@p11799
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p11491 (Enclosure.sfrac false 1 16))))
  p11650

noncomputable def p11801 :=
@p11800 p976 p11651 p5171
  1090143749475 1099511627776 8072186989 56693568307200000000
  p11790 p8122 p11792 p5920

noncomputable def p11802 :=
p11801
  (p11657 d144
    (p11659 (p11661 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (@p11664 2180287498950 2199023255552 529018846511104
    p2689 1090143749475 1099511627776 8072186989
    56693568307200000000 (p11690 (Eq.refl true))
    (Eq.refl true))

noncomputable def p11803 :=
@Enclosure.Real.IsNear.mulLit_ff p11570
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
      (Enclosure.sfrac false 12 1)))
  p11720 p976 p11715

noncomputable def p11804 :=
nat_lit 4441521672551311895452221

noncomputable def p11805 :=
nat_lit 41556825049252877880524800000000

noncomputable def p11806 :=
@p11494
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p11491 (Enclosure.sfrac false 1 16))))
  15505768149147

noncomputable def p11807 :=
@p11806 4398046511104 3285 4398046511104 286443188743
  2199023255552 8072186989 56693568307200000000 p11804
  p7541 24904122733315166491833 p11805

noncomputable def p11808 :=
p11807
  (p11581
    (@Enclosure.Real.IsNear.neg p11498 false 15505768149147 4398046511104
      3285 4398046511104 (p11608 (Eq.refl true))))
  (@p11526 286443188743 2199023255552 529018846511104
    p2689 286443188743 2199023255552 8072186989
    56693568307200000000 (p11711 (Eq.refl true))
    (Eq.refl true))

noncomputable def p11809 :=
@p11803 p2854 p11804 p7541
  24904122733315166491833 p11805 p11793 p7523
  p11794 p11795
  (@p11722 true p11720 p976 p11715
    p2854 (p11737 (Eq.refl true)))
  (@p11492 false p11804 p7541
    24904122733315166491833 p11805
    (BSN.correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
        (Enclosure.sfrac false 12 1))
      (p11493 (Eq.refl true) (Eq.refl true)
        (p11275 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p11808 (Eq.refl true)))

noncomputable def p11810 :=
p11789
  (p11581
    (@Enclosure.Real.IsNear.neg p11498 false 15505768149147 4398046511104
      3285 4398046511104 (p11608 (Eq.refl true))))
  (p11797
    (@p11798 true p11790 p8122 p11792
      p5920 (p11802 (Eq.refl true)))
    (p11809 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p11811 :=
p11781
  (@p11782 p11715 p2854 p11720
    p982 p11715 p2908
    (Enclosure.Real.IsNear.const false 2 1)
    (@p11722 true p11720 p976 p11715
      p2854 (p11737 (Eq.refl true)))
    (Eq.refl true))
  (@p11784 false p11778 p5277 p11779
    p11780
    (BSN.deriv_correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
        (Enclosure.sfrac false 12 1))
      (p11493 (Eq.refl true) (Eq.refl true)
        (p11275 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p11810 (Eq.refl true)))

noncomputable def p11812 :=
nat_lit 975451495810756201976323374454066307190775

noncomputable def p11813 :=
nat_lit 2480261372704163797402992341014255664491783348934292141418771

noncomputable def p11814 :=
@Enclosure.Real.IsNear.mulLit_ff p11572
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
      (Enclosure.sfrac false 12 1)))
  p11812 p5940 p11813

noncomputable def p11815 :=
@Enclosure.Real.IsNear.neg
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 4 1)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
          (Enclosure.sfrac false 12 1)))))

noncomputable def p11816 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 4 1)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
        (Enclosure.sfrac false 12 1))))
  p1068

noncomputable def p11817 :=
@p11816 p1070 p1071 p1072
  1247459198911 4398046511104 3405780739 56693568307200000000
  p11812 p5940 p11813 p2961

noncomputable def p11818 :=
p11817 d148
  (@p11502 1247459198911 4398046511104 223201246511104
    p2689 1247459198911 4398046511104 3405780739
    56693568307200000000
    (p11593 (p11605 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p11819 :=
@p11814 p2961 p11804 p7541
  24904122733315166491833 p11805 p11750 p7486
  p11751 p11752
  (@p11815 true p11812 p5940 p11813
    p2961 (p11818 (Eq.refl true)))
  (@p11492 false p11804 p7541
    24904122733315166491833 p11805
    (BSN.correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
        (Enclosure.sfrac false 12 1))
      (p11493 (Eq.refl true) (Eq.refl true)
        (p11275 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p11808 (Eq.refl true)))

noncomputable def p11820 :=
p11746
  (p11581
    (@Enclosure.Real.IsNear.neg p11498 false 15505768149147 4398046511104
      3285 4398046511104 (p11608 (Eq.refl true))))
  (p11754
    (p11776 (p11811 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true))
    (p11819 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p11821 :=
p11719
  (@p11721 p11715 p2854 p11713
    p976 p11715 p2846
    (Enclosure.Real.IsNear.const false 3 1)
    (@p11722 true p11720 p976 p11715
      p2854 (p11737 (Eq.refl true)))
    (Eq.refl true))
  (@p11741 false p11716 p7449 p11717
    p11718
    (BSN.iteratedDeriv_two_correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
        (Enclosure.sfrac false 12 1))
      (p11493 (Eq.refl true) (Eq.refl true)
        (p11275 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p11820 (Eq.refl true)))

noncomputable def p11822 :=
@p11633 p11619 p11579
  (@p11642 p11627 p11628
    (p11691 (Eq.refl true)) (p11712 (Eq.refl true))
    (Eq.refl true) (Eq.refl true))
  (p11821 (Eq.refl true)) (Eq.refl true) (Eq.refl true)

noncomputable def p11823 :=
nat_lit 2926354487432268605928970123362198921572325

noncomputable def p11824 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 3 1) p11572)
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
      (Enclosure.sfrac false 12 1)))
  p11823

noncomputable def p11825 :=
@p11824 p5940 p11813 p2972
  p11778 p5277 p11779 p11780
  p11620 p7351 p11621 p11622

noncomputable def p11826 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 3 1) p11572
  3 1 0 1 p11812 p5940

noncomputable def p11827 :=
p11825
  (@p11826 p11813 p2961 p11823
    p5940 p11813 p2972
    (Enclosure.Real.IsNear.const false 3 1)
    (@p11815 true p11812 p5940 p11813
      p2961 (p11818 (Eq.refl true)))
    (Eq.refl true))
  (@p11784 false p11778 p5277 p11779
    p11780
    (BSN.deriv_correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
        (Enclosure.sfrac false 12 1))
      (p11493 (Eq.refl true) (Eq.refl true)
        (p11275 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p11810 (Eq.refl true)))

noncomputable def p11828 :=
nat_lit 1458096217646149604534774970843134913412784487483833296875

noncomputable def p11829 :=
nat_lit 66933339513107884673623980071788364113095347571461702320849730280374828631672510479557

noncomputable def p11830 :=
@Enclosure.Real.IsNear.mulLit_tf p11574
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
      (Enclosure.sfrac false 12 1)))
  p11828 p2977 p11829

noncomputable def p11831 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 8 1)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi) Real.pi))
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
        (Enclosure.sfrac false 12 1))))

noncomputable def p11832 :=
@p11831 p1059 p1061 p1062
  p1063 2108711612625 2199023255552 3405780739
  56693568307200000000 p11828 p2977 p11829

noncomputable def p11833 :=
@p11832 p2980 d149
  (@p11725 4217423225250 4398046511104 223201246511104
    p2689 2108711612625 2199023255552 3405780739
    56693568307200000000
    (p11727 (p11736 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p11834 :=
@p11830 p2980 p11804 p7541
  24904122733315166491833 p11805 p11612 p7342
  p11613 p11614 (p11833 (Eq.refl true))
  (@p11492 false p11804 p7541
    24904122733315166491833 p11805
    (BSN.correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
        (Enclosure.sfrac false 12 1))
      (p11493 (Eq.refl true) (Eq.refl true)
        (p11275 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p11808 (Eq.refl true)))

noncomputable def p11835 :=
p11580
  (p11581
    (@Enclosure.Real.IsNear.neg p11498 false 15505768149147 4398046511104
      3285 4398046511104 (p11608 (Eq.refl true))))
  (p11616
    (@p11624 p11611 p11579 p11822
      (p11827 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true))
    (p11834 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p11836 :=
@p11563 p11556
  (@p11575 false p11560 p7287 p11561
    p11562
    (BSN.iteratedDeriv_three_correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
        (Enclosure.sfrac false 12 1))
      (p11493 (Eq.refl true) (Eq.refl true)
        (p11275 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p11835 (Eq.refl true)))

noncomputable def p11837 :=
@p11554 p11555 p11556 676147647 8589934592
  1 8589934592 p11486 p9972 p11487
  p11464
  (@p11558 p7279 p11555 p11556
    (BSN.correctionLinear_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11272
        (Enclosure.sfrac false 12 1)))
    (@Enclosure.Real.IsNear.neg p11557 false p11553 p7279
      p11555 p11556
      (p11836 d150 (Eq.refl true))))

noncomputable def p11838 :=
@Enclosure.Real.IsNear.recentre' (@Inv.inv.{0} Real Real.instInv p11272) false
  1352295294 17179869184 2 17179869184 676147647 8589934592

noncomputable def p11839 :=
@Enclosure.Real.IsNear.inv_image p11272 218256993519 17179869184 41
  17179869184 676147646 676147648 8589934592
  (p11480 (Eq.refl true)) (Eq.refl true) (Eq.refl true)

noncomputable def p11840 :=
p11552
  (p11837
    (@p11838 1 8589934592
      (p11839 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (Eq.refl true))
    (Eq.refl true))

noncomputable def p11841 :=
@p11465 p11267
  (@p11467 8589934592
    (@p2563 1 0 1
      (BSN.neg_one_pow_even_mk 12 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1))
    p11483 (Eq.refl true))
  (p11840 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p11842 :=
@p11274 p11264 p11266 p11267
  (BSN.hardyZApproximantRS_eq
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
      true 5)
    12
    (p11275 (Eq.refl true) (Eq.refl true)
      (Eq.refl true)))
  (p11460 p11841 (Eq.refl true) (Eq.refl true))

theorem d195 : p11265 p11266 p11267 :=
@p11268 p11264 p11266 p11267
  (@Eq.refl.{1} Real
    (hardyZApproximantRS
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
        true 5)))
  p11842

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

noncomputable def p11852 :=
nat_lit
  106789525910872097432163308382423052494890622847416794440128155848720884111866223304347282745560769552308971517522884062482192139645413330857945573160485446930396513771474917277438937459

noncomputable def p11853 :=
nat_lit
  33992831540273094316133645219357992149093959534530043084764424844825827831094543535306400144974674282808917087119776064982181077609773263322209278641061590524405201333465166018030600192

noncomputable def p11854 :=
Enclosure.Real.IsNear
  (hardyZApproximantRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
      true 5))
  false p11852 p11853

noncomputable def p11855 :=
nat_lit
  3187589706806057220850143802754006973731689831050884778770420482259649637372364592163366264865110372488673413251209736308804459301867004710632627931075868783749775575733886084937753117035479785455342390260678922671514389790806502092665461

noncomputable def p11856 :=
nat_lit
  988028952988604073610936414365456905935668532635875421378422435079148710279168808640116120278705990592979880788780691382483383349777380626201605061445702960045411532800000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p11857 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZApproximantRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
      true 5))
  (hardyZApproximantRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
      true 5))
  false p11852

noncomputable def p11858 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
  (Zeta.RiemannSiegel.mainSumOfPhase
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
      true 5)
    12)

noncomputable def p11859 :=
@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p11860 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (@HPow.hPow.{0, 0, 0} Real Nat Real
    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
    (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)))
    12)
  (p11859
    (@Neg.neg.{0} Real Real.instNeg
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
        (@OfNat.ofNat.{0} Real 4
          (@instOfNatAtLeastTwo.{0} Real 4 Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))))))

noncomputable def p11861 :=
Real.sqrt
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p11862 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p11860
  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
        (Enclosure.sfrac false 12 1)))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Zeta.RiemannSiegel.correctionLinear
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
          (Enclosure.sfrac false 12 1)))
      (@Inv.inv.{0} Real Real.instInv p11861)))

noncomputable def p11863 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZApproximantRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
      true 5))
  (p11858 p11862) false p11852

noncomputable def p11864 :=
@BSN.floor_sqrt_eq_dec
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
    true 5)
  101532300 100000 12
  (Enclosure.sfrac_ofScientific_eq 101532300 5 100000 (Eq.refl true))

noncomputable def p11865 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (Zeta.RiemannSiegel.mainSumOfPhase
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
      true 5)
    12)

noncomputable def p11866 :=
nat_lit
  4430168636744157703335894010630820823303448248221500104881336716242011288705865874501883644326529385444935136247722226596755503348963252896313427161839790894487775503032875729136285325

noncomputable def p11867 :=
nat_lit
  51436557277042562660603360210791316029106210060651717115843274827137100343928166069186512292539460995225200436611259787372722005444920870758796537399853295544975575733886084937753117035479785455342390260678922671514389790806502092665461

noncomputable def p11868 :=
nat_lit
  458657521342540269310066988033669671702046432226725530201505059419047320692671434619204634018648594407759593955156277979960635822165315292437303858472260354049996614960898387390905595023394340864

noncomputable def p11869 :=
@p11865 p11862 14052520167 4294967296 109063
  34359738368 p11866 p11853 p11867
  p11856 p11868 p11852

noncomputable def p11870 :=
@Enclosure.Real.IsNear.of_eq
  (Zeta.RiemannSiegel.mainSumOfPhase
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
      true 5)
    12)

noncomputable def p11871 :=
@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
      true 5)
    12)

noncomputable def p11872 :=
p11871
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
      true 5)
    12)

noncomputable def p11873 :=
@p11870 p11872 false 14052520167 4294967296
  109063 34359738368
  (BSN.main_sum_of_phase_eq
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
      true 5)
    12)

noncomputable def p11874 :=
@Enclosure.Real.IsNear.addLit_ff
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
      true 5)
    12)

noncomputable def p11875 :=
@p11874
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
      true 5)
    12)

noncomputable def p11876 :=
@p11875 224840322672 137438953472 218126 137438953472
  224840322672 137438953472 218126 137438953472
  61803637292692949434368 14052520167 4294967296

noncomputable def p11877 :=
BSN.mainSumRS_step
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
      true 5))
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
    true 5)
  Real.cos BSN.quadSignNeg

noncomputable def p11878 :=
p11877 11 12 101532300 100000 286
  137438953472 68719476736 2305843009213693952 false 284972482062934
  3364

noncomputable def p11879 :=
p11878 341522969406 43 39675208392 8 false
  262887946107 204541 true 39503267381 7244019458077122842 1

noncomputable def p11880 :=
p11879 false 131800833793 true false 224840322672 218126
  BSN.abs_quadSignNeg (BSN.cos_quad_nat2 286 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 131800833793 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101532300 5 100000 (Eq.refl true))
  (Eq.refl true)

noncomputable def p11881 :=
BSN.mainSumRS_step2
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
      true 5))
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
    true 5)
  Real.cos Real.sin

noncomputable def p11882 :=
p11881 BSN.quadSignPos BSN.quadSignNeg 9 10 11 101532300
  100000 168 229 137438953472 68719476736

noncomputable def p11883 :=
p11882 2305843009213693952 false 284972482062934 3364
  316464885454 43 43462013224 8 329564216814 43
  41439403656

noncomputable def p11884 :=
p11883 8 false 266565396731 175474 true 72309481122
  true 203157095938 7244019458077122842 1 false

noncomputable def p11885 :=
p11884 118851940164 false false 136849690388 true false
  262887946107 204541 BSN.abs_quadSignPos
  (BSN.cos_quad_nat0 168 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 118851940164 137438953472)

noncomputable def p11886 :=
BSN.mainSumRS_step2
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
      true 5))
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
    true 5)
  Real.cos Real.cos

noncomputable def p11887 :=
p11886 BSN.quadSignPos BSN.quadSignPos 7 8 9 101532300
  100000 24 100 137438953472 68719476736

noncomputable def p11888 :=
p11887 2305843009213693952 false 284972482062934 3364
  285796269294 43 48592008000 16 301984246446 43
  45812984488

noncomputable def p11889 :=
p11888 8 false 175788918366 143147 true 21716986921
  true 50208664122 7244019458077122842 1 false

noncomputable def p11890 :=
p11889 135726749488 false false 128369477677 false false
  266565396731 175474 BSN.abs_quadSignPos
  (BSN.cos_quad_nat0 24 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 135726749488 137438953472)

noncomputable def p11891 :=
BSN.mainSumRS_step2
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
      true 5))
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
    true 5)
  Real.sin Real.cos

noncomputable def p11892 :=
p11891 BSN.quadSignNeg BSN.quadSignNeg 5 6 7 101532300
  100000 161 62 137438953472 68719476736

noncomputable def p11893 :=
p11892 2305843009213693952 false 284972482062934 3364
  246257546308 43 56109217800 8 267443854420 43
  51947041624

noncomputable def p11894 :=
p11893 8 false 279471380797 106157 false
  183466246007 false 45492058770 7244019458077122842 1 false

noncomputable def p11895 :=
p11894 133632378890 true false 129978544812 true false
  175788918366 143147 BSN.abs_quadSignNeg
  (BSN.cos_quad_nat1 161 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 133632378890 137438953472)

noncomputable def p11896 :=
BSN.mainSumRS_step2
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
      true 5))
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
    true 5)
  Real.sin Real.sin

noncomputable def p11897 :=
p11896 BSN.quadSignPos BSN.quadSignPos 3 4 5 101532300
  100000 423 279 137438953472 68719476736

noncomputable def p11898 :=
p11897 2305843009213693952 false 284972482062934 3364
  190530846192 42 68719476728 8 221199462352 42
  61464568544

noncomputable def p11899 :=
p11898 16 false 156469965089 62550 false
  201252530528 false 150660036328 7244019458077122842 1 false

noncomputable def p11900 :=
p11899 136660381400 false false 122248575549 false false
  279471380797 106157 BSN.abs_quadSignPos
  (BSN.cos_quad_nat3 423 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 136660381400 137438953472)

noncomputable def p11901 :=
p11896 BSN.quadSignPos BSN.quadSignNeg 1 2 3 101532300
  100000 871 609 137438953472 68719476736

noncomputable def p11902 :=
p11901 2305843009213693952 false 284972482062934 3364
  95265423088 42 97184016000 16 150992123216 42
  79350416784

noncomputable def p11903 :=
p11902 16 false 137438135216 3418 false 208333446737
  false 190547150032 7244019458077122842 1 false

noncomputable def p11904 :=
p11903 137231348507 false false 135109293977 true false
  156469965089 62550 BSN.abs_quadSignPos
  (BSN.cos_quad_nat3 871 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 137231348507 137438953472)

noncomputable def p11905 :=
@Enclosure.Real.IsNear.recentre'
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
      true 5)
    1)

noncomputable def p11906 :=
@Enclosure.Real.IsNear.of_eq
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
      true 5)
    1)

noncomputable def p11907 :=
@p11906
  (Real.cos
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
        true 5)))
  false 8589883451

noncomputable def p11908 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
        true 5)))
  false 17179766902

noncomputable def p11909 :=
@Enclosure.Real.IsNear.cos_image
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
      true 5))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 17810780128933)
    (@Nat.cast.{0} Real Real.instNatCast 8589934592))
  false 17810780128933

noncomputable def p11910 :=
nat_lit 40920272130144626400119739306023663102786876290234663695669

noncomputable def p11911 :=
nat_lit 19735377032349731253597298455345433733873298231525376000

noncomputable def p11912 :=
@Enclosure.Real.IsNear.recentre'
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
      true 5))
  false p11910 p11911

noncomputable def p11913 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 101532300 400000)
      (Real.log (Enclosure.sfrac false 41235241773160000 160000000000)))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 1 4)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 1 2) Real.pi)
        (Real.arctan
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@Nat.cast.{0} Real Real.instNatCast 100000)
            (@Nat.cast.{0} Real Real.instNatCast 203064600))))))

noncomputable def p11914 :=
nat_lit 517919932899375601702919362964640000000000000000

noncomputable def p11915 :=
nat_lit 3155136477260135686193643886421059072320000000000000

noncomputable def p11916 :=
@Enclosure.Real.IsNear.of_eq
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
      true 5))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (p11913 (Enclosure.sfrac false 101532300 200000))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 101532300 200000) (Real.log Real.pi)))
    (Enclosure.sfrac true p11914 p11915))
  false

noncomputable def p11917 :=
BSN.riemannSiegelThetaApproximant_two_zero_mk
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
    true 5)
  101532300 100000 41235241773160000 160000000000

noncomputable def p11918 :=
p11917 203064600 400000 200000 p11914
  p11915
  (Enclosure.sfrac_ofScientific_eq 101532300 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p11919 :=
@Enclosure.Real.IsNear.addLit_ft_p
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (p11913 (Enclosure.sfrac false 101532300 200000))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 101532300 200000) (Real.log Real.pi)))
  (Enclosure.sfrac true p11914 p11915) 37351916126040853019421
  18014398509481984000

noncomputable def p11920 :=
nat_lit 117850383734816524032344849201348149736026203715875831443526720000000000000

noncomputable def p11921 :=
@p11919 1693455168546939839 p4831 p11914
  p11915 0 1 p11920 p11910
  p11911 1693455168546939839 p4831

noncomputable def p11922 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (p11913 (Enclosure.sfrac false 101532300 200000))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 101532300 200000) (Real.log Real.pi))
  1912828753798647915429 720575940379279360 1279723362703 132000000000000000000

noncomputable def p11923 :=
nat_lit 205344330501479011428295741255188480

noncomputable def p11924 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 101532300 400000)
      (Real.log (Enclosure.sfrac false 41235241773160000 160000000000)))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 1 4)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 1 2) Real.pi)
        (Real.arctan
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@Nat.cast.{0} Real Real.instNatCast 100000)
            (@Nat.cast.{0} Real Real.instNatCast 203064600))))))

noncomputable def p11925 :=
@p11924 (Enclosure.sfrac false 101532300 200000)
  56965935413887586106141 18014398509481984000 1279723362703
  132000000000000000000 101532300 200000 0

noncomputable def p11926 :=
nat_lit 9564143768993239577145000000

noncomputable def p11927 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 101532300 400000)
    (Real.log (Enclosure.sfrac false 41235241773160000 160000000000)))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 1 4)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 1 2) Real.pi)
      (Real.arctan
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@Nat.cast.{0} Real Real.instNatCast 100000)
          (@Nat.cast.{0} Real Real.instNatCast 203064600)))))
  56973007433823779922141

noncomputable def p11928 :=
nat_lit 128275882751397937307325342555693907968

noncomputable def p11929 :=
@p11927 18014398509481984000 423241115401 44000000000000000000
  884002492024227 2251799813685248 20000033 264000000000000000
  p11928 56965935413887586106141 18014398509481984000 1279723362703

noncomputable def p11930 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 101532300 400000)
  (Real.log (Enclosure.sfrac false 41235241773160000 160000000000)) 101532300
  400000 0 1 56113185098558567 4503599627370496

noncomputable def p11931 :=
nat_lit 30848549743706058496719978496

noncomputable def p11932 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast 41235241773160000)
      (@Nat.cast.{0} Real Real.instNatCast 160000000000)))
  false p11931 p2333

noncomputable def p11933 :=
BSN.log_rat_reduce_isNear 41235241773160000 160000000000 17 82470483546320000
  41943040000000000 46463158709 68719476736 24973259072661432
  36028797018963968 26400000000 1000000000000000

noncomputable def p11934 :=
nat_lit
  921373747723362096117184891834548173008988274073398951334570924648119719305419702708083243341872259244164959613085428589557748309478652525976439856148569896210665620601464216982480265494619140002624701511373771111415297405243434404778445350039398563308883078076842735714155956614696120877056000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p11935 :=
nat_lit
  34835866598389105209837249013848513238856434329025664104215281506596898987842935325946837286671551992052091627347623740609264282504464965665813095637146013953285723236470480423687965397468404029007019188853084073108322500240210553767497123386970994123009042444205350257246170559195867879833600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p11936 :=
nat_lit
  769313983356480955443898977807109271910010417478407852558520267572373424035192423963497144385434359182922978003585860857009664129543141985683295021844229315538393829324197288273254464640209918592095872651115867760350863597730905935219435715812940468179011093397371488155700559872000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p11937 :=
BSN.log_dyadic_bound 20263721773160000 62206761773160000 12 11
  p11934 68719476736 26400000000 p11935 p11936
  46463158709 82470483546320000

noncomputable def p11938 :=
p11937 41943040000000000 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p11939 :=
@BSN.binarySplit_of_base11 (BSN.artanhP 20263721773160000) (BSN.artanhQ 62206761773160000)
  0 11 p11935 p11934 p11936
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p11940 :=
p11933 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p11938 (p11939 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

noncomputable def p11941 :=
@p11930 1250561 33000000000000000 56973007433823779922141
  18014398509481984000 423241115401 44000000000000000000
  (Enclosure.Real.IsNear.const false 101532300 400000)
  (BSN.isNear_log_sfrac 41235241773160000 160000000000 56113185098558567
    4503599627370496 1250561 33000000000000000 false
    (@p11932 1000448800000000 p2422 56113185098558567
      4503599627370496 1250561 33000000000000000
      (p11940 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p11942 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 1 4)
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 1 2) Real.pi)
    (Real.arctan
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@Nat.cast.{0} Real Real.instNatCast 100000)
        (@Nat.cast.{0} Real Real.instNatCast 203064600))))
  1 4

noncomputable def p11943 :=
@p11942 0 1 884002492024227 562949953421312 20000033
  66000000000000000 884002492024227 2251799813685248 20000033
  264000000000000000 (Enclosure.Real.IsNear.const false 1 4)

noncomputable def p11944 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 1 2) Real.pi)
  (Real.arctan
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast 100000) (@Nat.cast.{0} Real Real.instNatCast 203064600)))
  884279719003555 562949953421312 1

noncomputable def p11945 :=
nat_lit 7593523585653111609360384

noncomputable def p11946 :=
@p11944 2000000000000000 4230148 8589934592 1
  3300000000 p11945 884002492024227 562949953421312 20000033
  66000000000000000
  (@p803 1 1000000000000000 884279719003555 562949953421312
    1 2000000000000000 (Enclosure.Real.IsNear.const false 1 2)
    BSN.pi_near_15 (Eq.refl true))

noncomputable def p11947 :=
BSN.arctan_dyadic_bound_f 100000 203064600 1 0 8589934592
  3300000000 0 1 1 0 1

noncomputable def p11948 :=
p11947 1 4230148 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)
  (@BSN.binarySplit_of_le (BSN.arctanEvenP 100000) (BSN.arctanEvenQ 203064600) 0
    0 (Eq.refl true))
  (@BSN.binarySplit_of_le (BSN.arctanOddP 100000) (BSN.arctanOddQ 203064600) 0 0
    (Eq.refl true))

noncomputable def p11949 :=
p11943
  (p11946
    (p11948 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p11950 :=
@p11922 79870626212504157 137438953472000 1015323
  68719476736000 p11923 37351916126040853019421 18014398509481984000
  1693455168546939839 p4831
  (@p11925 1 p11926 1912828753798647915429
    720575940379279360 1279723362703 132000000000000000000
    (@p11929 132000000000000000000 p11941 p11949
      (Eq.refl true) (Eq.refl true))
    (Enclosure.Real.IsNear.const false 101532300 200000) (Eq.refl true)
    (Eq.refl true))

noncomputable def p11951 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 101532300 200000) (Real.log Real.pi)
  101532300 200000 0 1 78665238759 68719476736

noncomputable def p11952 :=
p11950
  (@p11951 1 34359738368 79870626212504157 137438953472000
    1015323 68719476736000
    (Enclosure.Real.IsNear.const false 101532300 200000) d91
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p11953 :=
@p11909 8589934592 211 8589934592 false 17179766902
  17179869184 1 3300000000
  (@p11912 1693455168546939839 p4831 17810780128933
    8589934592 211 8589934592
    (@p11916 p11910 p11911 1693455168546939839
      p4831
      (p11918 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p11921 (p11952 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p11914 p11915)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p11954 :=
nat_lit 1940279943014630980883316736

noncomputable def p11955 :=
BSN.cos_reduce3
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 17810780128933)
    (@Nat.cast.{0} Real Real.instNatCast 8589934592))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast p11954)
    (@Nat.cast.{0} Real Real.instNatCast p2445))
  226375608064910080 72057594037927936 false

noncomputable def p11956 :=
BSN.sin_reduce_arg_pos_rat_q3 17810780128933 8589934592 226375608064910080
  72057594037927936 329 p11954 p2445
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p11957 :=
nat_lit
  1129332934303392595250541167977934566667199839818173564232429688787270414260360838304459386570230975928876661096984427982258057061985462131141109498549460822673590724202496

noncomputable def p11958 :=
nat_lit
  790997431747568477042250623839166422495404333317474615848540061309068608354747174073262330343686350979244951406716101477419151497573219466112194481987669813346308096

noncomputable def p11959 :=
nat_lit
  5639709352458894272874708089227575329527739134417506585146672332964651216328718853700318010370517409351668830238733553871525378631183399156703249396140545045563575101689856

noncomputable def p11960 :=
BSN.sin_dyadic_bound_f 55146072754002 35184372088832 4 3 17179869184
  6606445313 p11957 p3100 p11958
  p11959 p3103

noncomputable def p11961 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 55146072754002) (BSN.sinEvenQ 35184372088832) 0
  3 p11957 p3100 p11958 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p11962 :=
p11960 p11958 17179766902 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p11961 (Eq.refl true))

noncomputable def p11963 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 55146072754002) (BSN.sinOddQ 35184372088832) 0
  3 p11959 p3103 p11958 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p11964 :=
@BSN.sin_arg_round false 17179766902 17179869184 p11954
  p2445 55146072754002 35184372088832 6606445313 6600000000
  (p11962 (p11963 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p11965 :=
p11955 17179766902 17179869184 329 1000000000000000
  6600000000 3300000000 p11956 BSN.pi_near_15 p11964
  (Eq.refl true) (Eq.refl true)

noncomputable def p11966 :=
@p11907 8589934592 2753476307 110729625600000000
  (BSN.main_sum_rs_one
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
      true 5))
  (@p11908 17179869184 704889934592 28346784153600000000
    8589883451 8589934592 2753476307 110729625600000000
    (p11953 (Enclosure.sfrac_false_div 17810780128933 8589934592)
      (p11965 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p11967 :=
@p11905 false 8589883451 8589934592 2753476307
  110729625600000000 137438135216 137438953472 3418 137438953472
  p11966 (Eq.refl true)

noncomputable def p11968 :=
p11904 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 609 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 135109293977 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101532300 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true) p11967
  (@p11912 1693455168546939839 p4831 284972482062934
    137438953472 3364 137438953472
    (@p11916 p11910 p11911 1693455168546939839
      p4831
      (p11918 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p11921 (p11952 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p11914 p11915)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p11969 :=
nat_lit
  12467276218869116984474496603160449336486979021728553803453488682159149021333184258389937605329463546675793108589796640799306909005104395001281

noncomputable def p11970 :=
nat_lit
  6685101234902137549369191749673461240604352768726115486329147334633688533387558194349589653762475773588828999710502650310994674116140481

noncomputable def p11971 :=
nat_lit
  62269193707780347769547607100539622300741222421950476097254127207168791821895055679289388083202843846231123950324578172641419006010919240277441

noncomputable def p11972 :=
BSN.sin_dyadic_bound_f 208333446737 137438953472 4 3 137438953472
  68719476736 p11969 p2504 p11970
  p11971 p2507

noncomputable def p11973 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 208333446737) (BSN.sinEvenQ 137438953472) 0
  3 p11969 p2504 p11970 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p11974 :=
p11972 p11970 137231348507 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p11973 (Eq.refl true))

noncomputable def p11975 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 208333446737) (BSN.sinOddQ 137438953472) 0
  3 p11971 p2507 p11970 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p11976 :=
nat_lit
  8720030705654341821187657627431811421310910909416145897935935247602967971379295786098124462298342593843376096547396475204343951462618865074176

noncomputable def p11977 :=
nat_lit
  2291023216537811653032628790107300568886463486193464473476190172852808866255991699237657903600096906027442526067446282302129205701246976

noncomputable def p11978 :=
nat_lit
  43567254465634565356458197073577296790756069490668352622912255242686072591315374632807915678951966796804477819818837363307422884782692406132736

noncomputable def p11979 :=
BSN.sin_dyadic_bound_f 190547150032 137438953472 4 3 137438953472
  68719476736 p11976 p2504 p11977
  p11978 p2507

noncomputable def p11980 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 190547150032) (BSN.sinEvenQ 137438953472) 0
  3 p11976 p2504 p11977 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p11981 :=
p11979 p11977 135109293977 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p11980 (Eq.refl true))

noncomputable def p11982 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 190547150032) (BSN.sinOddQ 137438953472) 0
  3 p11978 p2507 p11977 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p11983 :=
p11968 d93 d95 d97 d99 d103
  (p11974 (p11975 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p11981 (p11982 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p11984 :=
p11900 BSN.abs_quadSignPos (BSN.cos_quad_nat3 279 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 122248575549 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101532300 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p11983 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p11912 1693455168546939839 p4831 284972482062934
    137438953472 3364 137438953472
    (@p11916 p11910 p11911 1693455168546939839
      p4831
      (p11918 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p11921 (p11952 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p11914 p11915)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p11985 :=
nat_lit
  10854333024003612123008448151787038962527597927388883068827274121664705208852653274403691689652375550577660207772051225131098980134065239228416

noncomputable def p11986 :=
nat_lit
  4414649190825644929086699142993653228079723072243088920279812316573609527345359399430115683894152123904181516321406038672520875570364416

noncomputable def p11987 :=
nat_lit
  54220717461859169361438430775617063958008863021073676431163565078784128271583318405254452086519134828440628380996079554347210448304876369739776

noncomputable def p11988 :=
BSN.sin_dyadic_bound_f 201252530528 137438953472 4 3 137438953472
  68719476736 p11985 p2504 p11986
  p11987 p2507

noncomputable def p11989 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 201252530528) (BSN.sinEvenQ 137438953472) 0
  3 p11985 p2504 p11986 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p11990 :=
p11988 p11986 136660381400 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p11989 (Eq.refl true))

noncomputable def p11991 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 201252530528) (BSN.sinOddQ 137438953472) 0
  3 p11987 p2507 p11986 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p11992 :=
nat_lit
  3405472680593938595273903912162452062671311296185368854170380545948166366426108927548982888799752341384894228394874735171487792924497192943616

noncomputable def p11993 :=
nat_lit
  136765580694637254001168249475932779288331538802998194716587694612077895040064833395778304445586588726119241007127678215374827333615616

noncomputable def p11994 :=
nat_lit
  17022339112882695407386555504912900263622691665595104520632403868363877247243124958140135266539648735390615285647023532990871966263709297278976

noncomputable def p11995 :=
BSN.sin_dyadic_bound_f 150660036328 137438953472 4 3 137438953472
  68719476736 p11992 p2504 p11993
  p11994 p2507

noncomputable def p11996 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 150660036328) (BSN.sinEvenQ 137438953472) 0
  3 p11992 p2504 p11993 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p11997 :=
p11995 p11993 122248575549 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p11996 (Eq.refl true))

noncomputable def p11998 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 150660036328) (BSN.sinOddQ 137438953472) 0
  3 p11994 p2507 p11993 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p11999 :=
p11984 d105 d107 d109 d111 d103
  (p11990 (p11991 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p11997 (p11998 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p12000 :=
p11895 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 62 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 129978544812 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101532300 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p11999 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p11912 1693455168546939839 p4831 284972482062934
    137438953472 3364 137438953472
    (@p11916 p11910 p11911 1693455168546939839
      p4831
      (p11918 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p11921 (p11952 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p11914 p11915)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p12001 :=
nat_lit
  7493045246035815407788720517287124111934017994306706204985506383386288024523012771963321254859486876659829071190059827658596177389772180082401

noncomputable def p12002 :=
nat_lit
  1454367285128381240712726393755475399594991645054908841672750504002686607904284000124093356963444698174016872319918497383556465186623201

noncomputable def p12003 :=
nat_lit
  37440926790607074210021215261385877826065773745816821868126409632679584124686944326937568514259482994743149138593469408393085096825191301172961

noncomputable def p12004 :=
BSN.sin_dyadic_bound_f 183466246007 137438953472 4 3 137438953472
  68719476736 p12001 p2504 p12002
  p12003 p2507

noncomputable def p12005 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 183466246007) (BSN.sinEvenQ 137438953472) 0
  3 p12001 p2504 p12002 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p12006 :=
p12004 p12002 133632378890 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p12005 (Eq.refl true))

noncomputable def p12007 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 183466246007) (BSN.sinOddQ 137438953472) 0
  3 p12003 p2507 p12002 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p12008 :=
nat_lit 2567403382664712355412433426266800390401421631779152632881317263212231636798718291632800000

noncomputable def p12009 :=
nat_lit 18343606783894549234603440662474860916569637292198082031765160373707758920688100000000

noncomputable def p12010 :=
nat_lit 7702173460780569277138831071919076221482431756062873502479888259315947494878313498698400000

noncomputable def p12011 :=
BSN.cos_dyadic_bound_f 45492058770 137438953472 3 2 137438953472
  68719476736 p12008 p2466 p12009
  p12010 p2469

noncomputable def p12012 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP 45492058770) (BSN.cosEvenQ 137438953472) 0
  2 p12008 p2466 p12009 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p12013 :=
p12011 p12009 129978544812 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p12012 (Eq.refl true))

noncomputable def p12014 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP 45492058770) (BSN.cosOddQ 137438953472) 0
  2 p12010 p2469 p12009 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p12015 :=
p12000 d113 d115 d117 d119 d103
  (p12006 (p12007 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p12013 (p12014 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p12016 :=
p11890 BSN.abs_quadSignPos (BSN.cos_quad_nat0 100 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 128369477677 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101532300 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p12015 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p11912 1693455168546939839 p4831 284972482062934
    137438953472 3364 137438953472
    (@p11916 p11910 p11911 1693455168546939839
      p4831
      (p11918 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p11921 (p11952 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p11914 p11915)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p12017 :=
nat_lit 133335894974609661175507132260689266470492859547835915140390252459789778007661076872831041

noncomputable def p12018 :=
nat_lit 49476225284312966186247213393423622452254067610687150379691094383530414120718442561

noncomputable def p12019 :=
nat_lit 400007585971378414900589024287641012564233674135372524046869997997180566962154989181608001

noncomputable def p12020 :=
BSN.cos_dyadic_bound_f 21716986921 137438953472 3 2 137438953472
  68719476736 p12017 p2466 p12018
  p12019 p2469

noncomputable def p12021 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP 21716986921) (BSN.cosEvenQ 137438953472) 0
  2 p12017 p2466 p12018 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p12022 :=
p12020 p12018 135726749488 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p12021 (Eq.refl true))

noncomputable def p12023 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP 21716986921) (BSN.cosOddQ 137438953472) 0
  2 p12019 p2469 p12018 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p12024 :=
nat_lit 3809499404119887322625000971690303233131079973765158820084327834028703845137025790047068416

noncomputable def p12025 :=
nat_lit 40385859652093234186765291436946925424245683167872284185517699242212618592626885959936

noncomputable def p12026 :=
nat_lit 11428417440640357781406629384488035805542391429929140715684612466687627110173892116369285376

noncomputable def p12027 :=
BSN.cos_dyadic_bound_f 50208664122 137438953472 3 2 137438953472
  68719476736 p12024 p2466 p12025
  p12026 p2469

noncomputable def p12028 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP 50208664122) (BSN.cosEvenQ 137438953472) 0
  2 p12024 p2466 p12025 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p12029 :=
p12027 p12025 128369477677 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p12028 (Eq.refl true))

noncomputable def p12030 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP 50208664122) (BSN.cosOddQ 137438953472) 0
  2 p12026 p2469 p12025 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p12031 :=
p12016 d121 d123 d125 d127 d103
  (p12022 (p12023 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p12029 (p12030 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p12032 :=
p11885 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 229 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 136849690388 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101532300 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p12031 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p11912 1693455168546939839 p4831 284972482062934
    137438953472 3364 137438953472
    (@p11916 p11910 p11911 1693455168546939839
      p4831
      (p11918 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p11921 (p11952 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p11914 p11915)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p12033 :=
nat_lit 16388885723636744321152336212143063816877327929184559518939932621600117648739578720132956416

noncomputable def p12034 :=
nat_lit 747415260839833439622473302828148039785966809382561119151574931926712378872069222727936

noncomputable def p12035 :=
nat_lit 49165162340388553296577763689823535154552411853934913434581494714936499521460992021953413376

noncomputable def p12036 :=
BSN.cos_dyadic_bound_f 72309481122 137438953472 3 2 137438953472
  68719476736 p12033 p2466 p12034
  p12035 p2469

noncomputable def p12037 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP 72309481122) (BSN.cosEvenQ 137438953472) 0
  2 p12033 p2466 p12034 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p12038 :=
p12036 p12034 118851940164 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p12037 (Eq.refl true))

noncomputable def p12039 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP 72309481122) (BSN.cosOddQ 137438953472) 0
  2 p12035 p2469 p12034 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p12040 :=
nat_lit
  11271742353608450790110301992387067246880829270050544039576163217095203157870691830046673990567885043467025106871744478416535460189743360249856

noncomputable def p12041 :=
nat_lit
  4942924230893880633317346684675899793070078285770300868297314952744803545626504479649122515209951058794480329382329033937326358092845056

noncomputable def p12042 :=
nat_lit
  56303776003150754978501652171874022988045016624081348622002532263319694448483704964624544239488407599145725458154264295171078645397779298390016

noncomputable def p12043 :=
BSN.sin_dyadic_bound_f 203157095938 137438953472 4 3 137438953472
  68719476736 p12040 p2504 p12041
  p12042 p2507

noncomputable def p12044 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 203157095938) (BSN.sinEvenQ 137438953472) 0
  3 p12040 p2504 p12041 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p12045 :=
p12043 p12041 136849690388 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p12044 (Eq.refl true))

noncomputable def p12046 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 203157095938) (BSN.sinOddQ 137438953472) 0
  3 p12042 p2507 p12041 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p12047 :=
p12032 d129 d131 d133 d135 d103
  (p12038 (p12039 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p12045 (p12046 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p12048 :=
p11880
  (p12047 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p11912 1693455168546939839 p4831 284972482062934
    137438953472 3364 137438953472
    (@p11916 p11910 p11911 1693455168546939839
      p4831
      (p11918 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p11921 (p11952 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p11914 p11915)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p12049 :=
nat_lit 1459763423598172241075367085976910926265279696843064631850208898953676656640918628038509921

noncomputable def p12050 :=
nat_lit 5930129079721737539717302872516079381965017110794049289767765373276228916810651174241

noncomputable def p12051 :=
nat_lit 4379278410536357279751021823324987746637075160494972307452047161330283417464922262813181281

noncomputable def p12052 :=
BSN.cos_dyadic_bound_f 39503267381 137438953472 3 2 137438953472
  68719476736 p12049 p2466 p12050
  p12051 p2469

noncomputable def p12053 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP 39503267381) (BSN.cosEvenQ 137438953472) 0
  2 p12049 p2466 p12050 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p12054 :=
p12052 p12050 131800833793 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p12053 (Eq.refl true))

noncomputable def p12055 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP 39503267381) (BSN.cosOddQ 137438953472) 0
  2 p12051 p2469 p12050 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p12056 :=
p12048 d137 d139 d103
  (p12054 (p12055 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true) (Eq.refl true)

noncomputable def p12057 :=
@p11869 p11853 p11855 p11856
  (p11873
    (@p11876 109063 34359738368
      (p12056 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (p12056 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true) (Eq.refl true)))

noncomputable def p12058 :=
@Enclosure.Real.IsNear.mulLit_ff p11860
  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
        (Enclosure.sfrac false 12 1)))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Zeta.RiemannSiegel.correctionLinear
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
          (Enclosure.sfrac false 12 1)))
      (@Inv.inv.{0} Real Real.instInv p11861)))

noncomputable def p12059 :=
nat_lit
  919404223917174402313576846215662977789952786686084549581981504477732154130717097975159704064436773876607138266976474822400502787000725238149472088102056125109160491149162775

noncomputable def p12060 :=
nat_lit
  10669214300106135266761755325760081261141829443686931846890725641564122273577371560916286155281077775469276106550959768667023908195894768383245200044431845813516990026064575738119173762234258366317133366411175457103442029895129

noncomputable def p12061 :=
nat_lit
  57510854268248895742635732421503455025124627435339813899389842704354593895793008189655148906092275317815358330773928399575139823705969647632539566923264819200000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p12062 :=
@p12058 4818521083 17179869184 1 17179869184
  p12059 p9769 p12060 p12061
  p11866 p11853 p11867

noncomputable def p12063 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HPow.hPow.{0, 0, 0} Real Nat Real
    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
    (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)))
    12)
  (p11859
    (@Neg.neg.{0} Real Real.instNeg
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
        (@OfNat.ofNat.{0} Real 4
          (@instOfNatAtLeastTwo.{0} Real 4 Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))))))

noncomputable def p12064 :=
@p12063 1 1 0 1 4818521083 17179869184
  1 17179869184 4818521083 17179869184 1

noncomputable def p12065 :=
@Enclosure.Real.IsNear.of_eq
  (p11859
    (@Neg.neg.{0} Real Real.instNeg
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
        (@OfNat.ofNat.{0} Real 4
          (@instOfNatAtLeastTwo.{0} Real 4 Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))))))

noncomputable def p12066 :=
BSN.rpow_neg_quarter_mk
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p12067 :=
p12066
  (BSN.t_div_two_pi_nonneg
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
      true 5)
    101532300 100000
    (Enclosure.sfrac_ofScientific_eq 101532300 5 100000 (Eq.refl true)))

noncomputable def p12068 :=
@Enclosure.Real.IsNear.recentre' (@Inv.inv.{0} Real Real.instInv (Real.sqrt p11861)) false
  4818521083 17179869184 1 17179869184 4818521083
  17179869184

noncomputable def p12069 :=
@Enclosure.Real.IsNear.recentre' (Real.sqrt p11861) false 61252799372
  17179869184 6 17179869184 15313199843 4294967296 3
  8589934592

noncomputable def p12070 :=
@Enclosure.Real.IsNear.sqrt_image
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p12071 :=
@Enclosure.Real.IsNear.of_eq
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p12072 :=
@p12071
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 101532300 100000)
    (@Inv.inv.{0} Real Real.instInv
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)))
  false 2776158185881269

noncomputable def p12073 :=
@p12072 17179869184000 1015323 17179869184000
  (BSN.t_div_two_pi_mk
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
      true 5)
    101532300 100000
    (Enclosure.sfrac_ofScientific_eq 101532300 5 100000 (Eq.refl true)))

noncomputable def p12074 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 101532300 100000)
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi))
  101532300 100000 0

noncomputable def p12075 :=
@p12074 1 2734261103 17179869184 1 17179869184
  2776158185881269 17179869184000 1015323 17179869184000
  (Enclosure.Real.IsNear.const false 101532300 100000) d142

noncomputable def p12076 :=
@p12070 2776158185881269 17179869184000 1015323 17179869184000
  109194819531 109194819572 8589934592
  (p12073 (p12075 (Eq.refl true))) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p12077 :=
@Enclosure.Real.IsNear.recentre' p11861 false 218389639103 17179869184
  41 17179869184 218389639103 17179869184 41 17179869184
  (p12076 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p12078 :=
@Enclosure.Real.IsNear.sqrt_image p11861 218389639103 17179869184 41
  17179869184 30626399683 30626399689 8589934592
  (p12077 (Eq.refl true)) (Eq.refl true) (Eq.refl true)

noncomputable def p12079 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt p11861) 15313199843 4294967296
  3 8589934592 2409260541 2409260542 8589934592
  (p12069
    (p12078 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p12080 :=
@p12065 (@Inv.inv.{0} Real Real.instInv (Real.sqrt p11861)) false
  4818521083 17179869184 1 17179869184 p12067
  (@p12068 1 17179869184
    (p12079 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p12081 :=
@Enclosure.Real.IsNear.addLit_ft_p
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
      (Enclosure.sfrac false 12 1)))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Zeta.RiemannSiegel.correctionLinear
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
        (Enclosure.sfrac false 12 1)))
    (@Inv.inv.{0} Real Real.instInv p11861))
  68685739192539547525

noncomputable def p12082 :=
nat_lit 95116024130064875520000000

noncomputable def p12083 :=
nat_lit
  1520974702526379183176190765939380993848212147295971216477199399905053564226898822874116075527882336898285743915809321742154879163135491460580750309543771863881324789499625

noncomputable def p12084 :=
nat_lit
  9356168900707321364382273519547210510330783494787521038310146076097370030889956546043104523183400784144134338344888703161856384508769262925789251306371217838996675354858579373057920744752788772377788803725152367814009965043

noncomputable def p12085 :=
nat_lit
  19170284756082965247545244140501151675041542478446604633129947568118197965264336063218382968697425105938452776924642799858379941235323215877513188974421606400000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p12086 :=
nat_lit
  135680115351101332012983584981393968842278794857228772679480852177510045405412913442333191714289503715748374737678503664920150396500345595882113248921411843317043688516843923052333797752386355200

noncomputable def p12087 :=
@p12081 147573952589676412928 17599173111496409371 p12082
  p12083 p9769 p12084 p12085
  p12086 p12059 p9769 p12060

noncomputable def p12088 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (@Inv.inv.{0} Real Real.instInv
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
          (Enclosure.sfrac false 12 1)))))

noncomputable def p12089 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
        (Enclosure.sfrac false 12 1))
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
        (Enclosure.sfrac false 12 1)))
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
      (Enclosure.sfrac false 12 1)))

noncomputable def p12090 :=
@Enclosure.Real.IsNear.of_eq
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
      (Enclosure.sfrac false 12 1)))
  (p12088
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p12089 (Enclosure.sfrac false 1 16)))))

noncomputable def p12091 :=
BSN.cos_two_pi_p_ne_zero_mk
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
    true 5)
  101532300 100000 12
  (Enclosure.sfrac_ofScientific_eq 101532300 5 100000 (Eq.refl true))

noncomputable def p12092 :=
@Enclosure.Real.IsNear.mulLit_tt
  (@Inv.inv.{0} Real Real.instInv
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
          (Enclosure.sfrac false 12 1)))))

noncomputable def p12093 :=
@p12092
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p12089 (Enclosure.sfrac false 1 16))))
  72548938615

noncomputable def p12094 :=
@p12093 17179869184 4695 17179869184 946750435
  8589934592 8123749489 221459251200000000 68685739192539547525
  147573952589676412928 17599173111496409371 p12082

noncomputable def p12095 :=
@Enclosure.Real.IsNear.of_eq
  (@Inv.inv.{0} Real Real.instInv
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
          (Enclosure.sfrac false 12 1)))))

noncomputable def p12096 :=
@Inv.inv.{0} Real Real.instInv
  (@Neg.neg.{0} Real Real.instNeg
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
          (Enclosure.sfrac false 12 1)))))

noncomputable def p12097 :=
@p12095 (@Neg.neg.{0} Real Real.instNeg p12096) true 72548938615
  17179869184 4695 17179869184
  (BSN.inv_eq_neg_inv_neg
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
          (Enclosure.sfrac false 12 1)))))

noncomputable def p12098 :=
@Enclosure.Real.IsNear.inv_image
  (@Neg.neg.{0} Real Real.instNeg
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
          (Enclosure.sfrac false 12 1)))))

noncomputable def p12099 :=
@Enclosure.Real.IsNear.neg
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
        (Enclosure.sfrac false 12 1))))
  true

noncomputable def p12100 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
        (Enclosure.sfrac false 12 1))))
  true

noncomputable def p12101 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
      (Enclosure.sfrac false 12 1)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 38425476009)
    (@Nat.cast.{0} Real Real.instNatCast 8589934592))
  false

noncomputable def p12102 :=
nat_lit 10815809964744382452621725

noncomputable def p12103 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
      (Enclosure.sfrac false 12 1)))
  false p12102

noncomputable def p12104 :=
nat_lit 1106429196836090252800523487

noncomputable def p12105 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
    (Enclosure.sfrac false 12 1))
  884279719003555 140737488355328 1

noncomputable def p12106 :=
@Enclosure.Real.IsNear.subLit_ff_p p11861 (Enclosure.sfrac false 12 1)
  218389639103 17179869184 41 17179869184 12 1 0

noncomputable def p12107 :=
@p12105 500000000000000 12231208895 17179869184 41
  17179869184 p12102 p2602 p12104
  p5018 d141
  (@p12106 1 12231208895 12231208895 17179869184 41
    17179869184 (p12077 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p12108 :=
@p12101 38425476009 8589934592 129 8589934592 true
  4068259451 17179869184 1 3300000000
  (@p12103 p2602 p12104 p5018
    38425476009 8589934592 129 8589934592
    (p12107 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div 38425476009 8589934592)

noncomputable def p12109 :=
nat_lit 1648591368937712126554800128

noncomputable def p12110 :=
BSN.cos_reduce2
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 38425476009)
    (@Nat.cast.{0} Real Real.instNatCast 8589934592))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast p12109)
    (@Nat.cast.{0} Real Real.instNatCast p2445))
  226375608064910080 72057594037927936 false

noncomputable def p12111 :=
BSN.sin_reduce_arg_pos_rat_q2 38425476009 8589934592 226375608064910080
  72057594037927936 0 p12109 p2445 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p12112 :=
nat_lit
  226354720131022837349570083111368908176471875305390763178745610932611153031223242296297023321753015686607108341760815479873071230459780208788400455961724055539554929789841

noncomputable def p12113 :=
nat_lit
  111984677353974067601212913882694340218878710805718481394708967763194333537648426466549471323584944526852523444759004958263533938528294443457657344342299016928873361

noncomputable def p12114 :=
nat_lit
  1371507342805922028829386477170481218657142489164429404393986724585573791106831750695922093194212128614798994883601626642159062338311650404279777893563683935856238495189905

noncomputable def p12115 :=
BSN.cos_dyadic_bound_f 46855784857419 35184372088832 4 3 17179869184
  6606445313 p12112 p2613 p12113
  p12114 p2616

noncomputable def p12116 :=
@BSN.binarySplit_of_base3 (BSN.cosEvenP 46855784857419) (BSN.cosEvenQ 35184372088832) 0
  3 p12112 p2613 p12113 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p12117 :=
p12115 p12113 4068259451 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p12116 (Eq.refl true))

noncomputable def p12118 :=
@BSN.binarySplit_of_base3 (BSN.cosOddP 46855784857419) (BSN.cosOddQ 35184372088832) 0
  3 p12114 p2616 p12113 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p12119 :=
@BSN.cos_arg_round false 4068259451 17179869184 p12109
  p2445 46855784857419 35184372088832 6606445313 6600000000
  (p12117 (p12118 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p12120 :=
p12110 4068259451 17179869184 0 1000000000000000
  6600000000 3300000000 p12111 BSN.pi_near_15 p12119
  (Eq.refl true) (Eq.refl true)

noncomputable def p12121 :=
@p12099 4068259451 17179869184 1696445057 110729625600000000
  (@p12100 4068259451 17179869184 434289934592
    28346784153600000000 4068259451 17179869184 1696445057
    110729625600000000
    (p12108 (p12120 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p12122 :=
@p12098 4068259451 17179869184 1696445057 110729625600000000
  36274466960 36274471655 8589934592 p12121
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p12123 :=
@Enclosure.Real.IsNear.recentre' p12096 false 72548938615 17179869184
  4695 17179869184 72548938615 17179869184 4695 17179869184
  (p12122 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p12124 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p12089 (Enclosure.sfrac false 1 16))))
  true

noncomputable def p12125 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p12089 (Enclosure.sfrac false 1 16)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Neg.neg.{0} Real Real.instNeg (@Nat.cast.{0} Real Real.instNatCast 451303609))
    (@Nat.cast.{0} Real Real.instNatCast 268435456))
  true

noncomputable def p12126 :=
nat_lit 69835850931931391244912067806173405

noncomputable def p12127 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p12089 (Enclosure.sfrac false 1 16)))
  true p12126

noncomputable def p12128 :=
nat_lit 46074238479654398010005417342254102137

noncomputable def p12129 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (p12089 (Enclosure.sfrac false 1 16)) 884279719003555
  140737488355328 1

noncomputable def p12130 :=
@Enclosure.Real.IsNear.subLit_tf
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
        (Enclosure.sfrac false 12 1))
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
        (Enclosure.sfrac false 12 1)))
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
      (Enclosure.sfrac false 12 1)))

noncomputable def p12131 :=
@p12130 (Enclosure.sfrac false 1 16) 60528097745150070655
  295147905179352825856 1707333767615 295147905179352825856 1 16
  0

noncomputable def p12132 :=
@Enclosure.Real.IsNear.subLit_ff_n
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
      (Enclosure.sfrac false 12 1))
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
      (Enclosure.sfrac false 12 1)))
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
    (Enclosure.sfrac false 12 1))
  149602471033127121025

noncomputable def p12133 :=
nat_lit 1039864801218043584301257195520

noncomputable def p12134 :=
@p12132 295147905179352825856 1002959131071 295147905179352825856
  12231208895 17179869184 41 17179869184 p12133
  60528097745150070655 295147905179352825856 1707333767615

noncomputable def p12135 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
    (Enclosure.sfrac false 12 1))
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
    (Enclosure.sfrac false 12 1))
  12231208895 17179869184 41

noncomputable def p12136 :=
@p12135 17179869184 12231208895 17179869184 41
  17179869184 149602471033127121025 295147905179352825856 1002959131071
  295147905179352825856
  (@p12106 1 12231208895 12231208895 17179869184 41
    17179869184 (p12077 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p12137 :=
p12136
  (@p12106 1 12231208895 12231208895 17179869184 41
    17179869184 (p12077 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p12138 :=
@p12134 295147905179352825856 (p12137 (Eq.refl true))
  (@p12106 1 12231208895 12231208895 17179869184 41
    17179869184 (p12077 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p12139 :=
@p12129 500000000000000 78974841818859622271 295147905179352825856
  1707333767615 295147905179352825856 p12126 p2630
  p12128 p2632 d141
  (@p12131 1 1263597469101753956336 78974841818859622271
    295147905179352825856 1707333767615 295147905179352825856
    (p12138 (Eq.refl true) (Eq.refl true))
    (Enclosure.Real.IsNear.const false 1 16) (Eq.refl true)
    (Eq.refl true))

noncomputable def p12140 :=
@p12125 451303609 268435456 625 17179869184 true
  946750435 8589934592 1 3300000000
  (@p12127 p2630 p12128 p2632
    451303609 268435456 625 17179869184
    (p12139 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_true_div 451303609 268435456)

noncomputable def p12141 :=
nat_lit
  5086557339230038869822179276911081868951757235097757742153545449213275418180852818384148422062040582633210278667684464093034643618061202688657320321

noncomputable def p12142 :=
nat_lit
  15207493910898943772408514932916795907872516077367179041497337572987785582714520667489429441430027511937547136632967505104166499053287056005398528000

noncomputable def p12143 :=
nat_lit
  2961426131327943166207745740393714943768901700442811901921729814840840838420625690842429157013149339609293542927840937437979498554327034241

noncomputable def p12144 :=
nat_lit
  51719036058602353241924301017542661863550847501826138806866627049363637424891981943580570014330957450629835060380174737571269294236620341760753658241

noncomputable def p12145 :=
nat_lit
  2326746568367538397178502784736269773904494959837178393349092648667131194155321662125882704538794209326444711904844028280937474355152919568825974784000

noncomputable def p12146 :=
BSN.cos_dyadic_bound_t 451303609 268435456 5 4 8589934592
  3300000000 p12141 p12142 p12143
  p12144 p12145

noncomputable def p12147 :=
@BSN.binarySplit_of_base4 (BSN.cosEvenP 451303609) (BSN.cosEvenQ 268435456) 0 4
  p12141 p12142 p12143 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p12148 :=
p12146 p12143 946750435 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p12147 (Eq.refl true))

noncomputable def p12149 :=
@BSN.binarySplit_of_base4 (BSN.cosOddP 451303609) (BSN.cosOddQ 268435456) 0 4
  p12144 p12145 p12143 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p12150 :=
p12140
  (BSN.cos_neg_of_bound 451303609 268435456 true 946750435 8589934592
    1 3300000000
    (p12148 (p12149 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p12151 :=
p12094
  (p12097
    (@Enclosure.Real.IsNear.neg p12096 false 72548938615 17179869184
      4695 17179869184 (p12123 (Eq.refl true))))
  (@p12124 946750435 8589934592 2079679869184
    56693568307200000000 946750435 8589934592 8123749489
    221459251200000000 (p12150 (Eq.refl true)) (Eq.refl true))

noncomputable def p12152 :=
@p12087 p12061
  (@p12090 false 68685739192539547525 147573952589676412928
    17599173111496409371 p12082
    (BSN.correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
        (Enclosure.sfrac false 12 1))
      (p12091 (Eq.refl true) (Eq.refl true)
        (p11864 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p12151 (Eq.refl true)))

noncomputable def p12153 :=
nat_lit
  18006707041978845036948646159484718247330960259625413496420688943631138608677083037719683562174237439657565029543380811359190035175171786198096538764992024102269625

noncomputable def p12154 :=
nat_lit
  1842755090244893238399196572748178169393027939656465052918069482541808673043041431682679065028153695088607604995490158642466105776330465152617887818082371115063181312

noncomputable def p12155 :=
@Enclosure.Real.IsNear.mulLit_tf
  (Zeta.RiemannSiegel.correctionLinear
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
      (Enclosure.sfrac false 12 1)))
  (@Inv.inv.{0} Real Real.instInv p11861) p12153 p12154

noncomputable def p12156 :=
nat_lit
  110508814568627841154094305336364979476426721590888108434612056424044087933004983311545025550372722818105926998228977298451694081779396694747164955531651913790556287021934304824707337671827896352137659268367059777251

noncomputable def p12157 :=
nat_lit
  17853718955147047757678892594297557766587978674514782273331608221044948292211011111008360021465853886621494569745513424145411645281429603581794713600000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p12158 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
      (Enclosure.sfrac false 12 1)))
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 96 1)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi)))

noncomputable def p12159 :=
@Enclosure.Real.IsNear.of_eq
  (Zeta.RiemannSiegel.correctionLinear
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
      (Enclosure.sfrac false 12 1)))
  (@Neg.neg.{0} Real Real.instNeg p12158) true p12153

noncomputable def p12160 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
      (Enclosure.sfrac false 12 1)))
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 96 1)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi)))

noncomputable def p12161 :=
nat_lit
  242451835769528446645531219424663394893095402109362376283350155079025583194925418955327331404832930943791562522994460679264165489977625898216053272720125

noncomputable def p12162 :=
nat_lit
  26187124863169134960105517574620793217733136368344518315866330944769070371237396439066160738607233257207093473020480568073738052367083144426628220715008

noncomputable def p12163 :=
nat_lit
  1487917550613730107660978110798064682241593624222035204174871512134976551270149276048072398935030031726033569797332006001962942093309269340569186506064846827574910942802941064391399684571014342688502691727

noncomputable def p12164 :=
nat_lit
  253716606197642814744297262937743053137580470128608315481693697123616691047388529668301657998566922268274404498036935594675066529382400000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p12165 :=
@p12160 p12161 p12162 p12163
  p12164 74269213037 70368744177664 1 70368744177664
  p12153 p12154 p12156

noncomputable def p12166 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p12167 :=
p12166
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p12168 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p12167
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p12169 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p12168
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p12089 (Enclosure.sfrac false 1 16)))))

noncomputable def p12170 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (Enclosure.sfrac false 3 1)
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p12171 :=
p12169
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p12170
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 4 1) Real.pi))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p12089 (Enclosure.sfrac false 1 16)))))

noncomputable def p12172 :=
@Neg.neg.{0} Real Real.instNeg
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
          (Enclosure.sfrac false 12 1)))))

noncomputable def p12173 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p12171
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 3 1) p12172)
    (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
        (Enclosure.sfrac false 12 1))))

noncomputable def p12174 :=
@Neg.neg.{0} Real Real.instNeg
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 4 1)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
          (Enclosure.sfrac false 12 1)))))

noncomputable def p12175 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p12173
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 3 1) p12174)
    (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
        (Enclosure.sfrac false 12 1))))

noncomputable def p12176 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 8 1)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi) Real.pi))
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
        (Enclosure.sfrac false 12 1))))

noncomputable def p12177 :=
@Enclosure.Real.IsNear.of_eq
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
      (Enclosure.sfrac false 12 1)))
  (p12088
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p12175
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p12176
        (Zeta.RiemannSiegel.correction
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
            (Enclosure.sfrac false 12 1))))))

noncomputable def p12178 :=
@p12092
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p12175
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p12176
      (Zeta.RiemannSiegel.correction
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
          (Enclosure.sfrac false 12 1)))))
  297160440153807

noncomputable def p12179 :=
nat_lit
  815895398607021927521647894377667825510520333295595387394615902877320732938318939709078739569098286591873609950093479312623637646185077875

noncomputable def p12180 :=
nat_lit
  372141426839350727961253789638658321589064376671906846864122981980487315514059736743009817965446945567110411062408283101969716033850703872

noncomputable def p12181 :=
nat_lit
  5006993650920873639966608876917746398943539879819412912753738919697564520709122878723976486440230561335306933063949849223003054014202765541858198726691870341079626977519393414295117857108801

noncomputable def p12182 :=
nat_lit
  3605529829508822313418608913163766560751077891618028779158943523322260077853066628510726701486062811856561502538013081600000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p12183 :=
@p12178 70368744177664 4695 70368744177664 p12179
  p12180 p12181 p12182 p12161
  p12162 p12163 p12164

noncomputable def p12184 :=
@p12095 (@Neg.neg.{0} Real Real.instNeg p12096) true 297160440153807
  70368744177664 4695 70368744177664
  (BSN.inv_eq_neg_inv_neg
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
          (Enclosure.sfrac false 12 1)))))

noncomputable def p12185 :=
nat_lit 475580120650324377600000000

noncomputable def p12186 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
      (Enclosure.sfrac false 12 1)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 314781498752345)
    (@Nat.cast.{0} Real Real.instNatCast 70368744177664))
  false

noncomputable def p12187 :=
nat_lit 44301557515130855929663705605

noncomputable def p12188 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
      (Enclosure.sfrac false 12 1)))
  false p12187

noncomputable def p12189 :=
nat_lit 9903520314283042199192993792

noncomputable def p12190 :=
nat_lit 1106859439174687881471425759

noncomputable def p12191 :=
nat_lit 302231454903657293676544000000000000000

noncomputable def p12192 :=
@Enclosure.Real.IsNear.subLit_ff_p p11861 (Enclosure.sfrac false 12 1)
  894523961652279 70368744177664 41 70368744177664 12 1
  0

noncomputable def p12193 :=
@p12071
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 101532300 100000)
    (@Inv.inv.{0} Real Real.instInv
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)))
  false 2274228785296622907

noncomputable def p12194 :=
@p12193 14073748835532800 1015323 70368744177664000
  (BSN.t_div_two_pi_mk
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
      true 5)
    101532300 100000
    (Enclosure.sfrac_ofScientific_eq 101532300 5 100000 (Eq.refl true)))

noncomputable def p12195 :=
@p12074 1 11199533475045 70368744177664 1
  70368744177664 2274228785296622907 14073748835532800 1015323
  70368744177664000 (Enclosure.Real.IsNear.const false 101532300 100000)
  d198

noncomputable def p12196 :=
@p12070 2274228785296622907 14073748835532800 1015323
  70368744177664000 447261980826119 447261980826160 35184372088832
  (p12194 (p12195 (Eq.refl true))) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p12197 :=
@Enclosure.Real.IsNear.recentre' p11861 false 894523961652279 70368744177664
  41 70368744177664 894523961652279 70368744177664 41
  70368744177664
  (p12196 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p12198 :=
@p12105 500000000000000 50099031520311 70368744177664 41
  70368744177664 p12187 p12189 p12190
  p12191 d197
  (@p12192 1 50099031520311 50099031520311 70368744177664
    41 70368744177664 (p12197 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p12199 :=
@p12186 314781498752345 70368744177664 129 35184372088832
  true 16663591407317 70368744177664 1 13516800000000
  (@p12188 p12189 p12190 p12191
    314781498752345 70368744177664 129 35184372088832
    (p12198 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div 314781498752345 70368744177664)

noncomputable def p12200 :=
nat_lit 13505260391528412525618633113600

noncomputable def p12201 :=
nat_lit 10141204801825835211973625643008

noncomputable def p12202 :=
BSN.cos_reduce2
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 314781498752345)
    (@Nat.cast.{0} Real Real.instNatCast 70368744177664))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast p12200)
    (@Nat.cast.{0} Real Real.instNatCast p12201))
  226375608064910080 72057594037927936 false

noncomputable def p12203 :=
BSN.sin_reduce_arg_pos_rat_q2 314781498752345 70368744177664 226375608064910080
  72057594037927936 0 p12200 p12201
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p12204 :=
nat_lit
  95110958557135467556138146109455703637993139419050124901767037618823679859367135167698739404179100892886956876854173618593925480085102400999286183209159854855792404847456036555172962114727268612401802716944636479415216785296171451176806654012421706907944640915948124209623859200000000000

noncomputable def p12205 :=
nat_lit
  724395325779541883127972740267467641917054236400314122627846279324277345529845529720229616430545782367401373900304422017855283570911757419651361948377693681253993101024836647459626987279301240215309090298978493065512302911076452246852449566697292461376960433893740547516518998105653248000

noncomputable def p12206 :=
nat_lit
  3388212070834351056041917395901435208513123025299590204916267507788705957973968383234962345445254824877311756388056607529291027766958930045695569325974603708724028198838169663739029961519182859732392116396108799852304631615073779535493513976217600000000000000000000000000000000

noncomputable def p12207 :=
nat_lit
  968922807833312004102395441100705439110277550229796193642831171797002591362526582991357877050702153240434842513094432823582587090295103887624197860942472685998151111192699422884965127421558395256166428140573376195610385765841965955464545129490070978527824015967737140934963363840000000000

noncomputable def p12208 :=
nat_lit
  110832484844269908118579829260922549213309298169248060762060480736614433866066366047195131313873504702212410206746576568731858386349498885206658378101787133231860944456800007061322929053733089752942290815743709439023382345394697193768424783704685746590674946385742303770027406710164946944000

noncomputable def p12209 :=
BSN.cos_dyadic_bound_f 191921293314982400 144115188075855872 5 4
  70368744177664 27060000000001 p12204 p12205
  p12206 p12207 p12208

noncomputable def p12210 :=
@BSN.binarySplit_of_base4 (BSN.cosEvenP 191921293314982400) (BSN.cosEvenQ 144115188075855872)
  0 4 p12204 p12205 p12206
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p12211 :=
p12209 p12206 16663591407317 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p12210 (Eq.refl true))

noncomputable def p12212 :=
@BSN.binarySplit_of_base4 (BSN.cosOddP 191921293314982400) (BSN.cosOddQ 144115188075855872)
  0 4 p12207 p12208 p12206
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p12213 :=
@BSN.cos_arg_round false 16663591407317 70368744177664 p12200
  p12201 191921293314982400 144115188075855872 27060000000001
  27033600000000
  (p12211 (p12212 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p12214 :=
p12202 16663591407317 70368744177664 0 1000000000000000
  27033600000000 13516800000000 p12203 BSN.pi_near_15 p12213
  (Eq.refl true) (Eq.refl true)

noncomputable def p12215 :=
@p12099 16663591407317 70368744177664 1696445057
  453548546457600000000
  (@p12100 16663591407317 70368744177664 1778851572088832
    p12185 16663591407317 70368744177664 1696445057
    453548546457600000000
    (p12199 (p12214 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p12216 :=
@p12098 16663591407317 70368744177664 1696445057
  453548546457600000000 148580220074556 148580220079251 35184372088832
  p12215 (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p12217 :=
@Enclosure.Real.IsNear.recentre' p12096 false 297160440153807 70368744177664
  4695 70368744177664 297160440153807 70368744177664 4695
  70368744177664
  (p12216 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p12218 :=
nat_lit
  42557869639175672694114382929462436704090371217521013570209431692599191752778256869511104318465645499851099819555771987132385553388311157875

noncomputable def p12219 :=
@Enclosure.Real.IsNear.subLit_tt_n p12175
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p12176
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
        (Enclosure.sfrac false 12 1))))
  p12218 p12180

noncomputable def p12220 :=
nat_lit
  4966132688114581593584377918045579216343091321601122913227373415272995602928290692224204438354036578474821578148793922911809036430802282946016836455968199091030255292828408454295117857108801

noncomputable def p12221 :=
nat_lit 13618954550753096726996382434158602719207964853274630556875156225418241246094420180625

noncomputable def p12222 :=
nat_lit 121416805764108066932466369176469931665150427440758720078238275608681517825325531136

noncomputable def p12223 :=
nat_lit
  722061087001964630690648604172337044852083905680741457654743471878324712549344174731811794094334140756889875943737016243

noncomputable def p12224 :=
nat_lit
  63713936459477097952240406748620611552931532717332212308858141409280000000000000000000000000000000000000000000000000000000000000

noncomputable def p12225 :=
nat_lit
  99063413136498308853325694695350836328260918260035955804549296047152724008208923318121711341558665538097581760731301740846036363702760811096955882204635924698777595134632306143537239206369102760240018724240616341897216000

noncomputable def p12226 :=
@p12219 p12220 p12182 p12221
  p12222 p12223 p12224 p12225
  p12179 p12180 p12181 p12182

noncomputable def p12227 :=
@Enclosure.Real.IsNear.subLit_tf p12173
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 3 1) p12174)
    (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
        (Enclosure.sfrac false 12 1))))

noncomputable def p12228 :=
nat_lit
  34007115918983263082930208064789345347570757533994967737570337658245069224849113088193457847558617261323675020908295588638443240117670517875

noncomputable def p12229 :=
nat_lit
  4827623211152695979517755991537974755062089998497874896749787274794567458731038351507213970607795407757696700726074406240457114918328314681039276646150130421331565514777626234773889057108801

noncomputable def p12230 :=
nat_lit
  13814487695427417164472781336970645072755085561544779836473772125992388522307654308844067432923929783381748610625

noncomputable def p12231 :=
nat_lit 601226901190101306339707032778070279008174732520529886901066488712245510429339761526706943586500787976175353856

noncomputable def p12232 :=
nat_lit
  52078342726241825867959401773252855023555390976118338299028163559670686744177675177065212407670065386634274404720146358555472951823177512466709726939088529

noncomputable def p12233 :=
nat_lit
  1355647442250600490411650605636441166179752215984680574798351469045340754992500577965050953728000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p12234 :=
nat_lit
  25586936084413884501914963147267977325451808083984921208970142274186762977725694963685876680577868313064244946013617304110796329647870730801091405531253849689405801000540153255337051894125979714525109660113897599537898288015383115825771937861206016000

noncomputable def p12235 :=
@p12227 p12228 p12180 p12229
  p12182 p12230 p12231 p12232
  p12233 p12234 p12218 p12180

noncomputable def p12236 :=
@Enclosure.Real.IsNear.subLit_tf p12171
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 3 1) p12172)
    (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
        (Enclosure.sfrac false 12 1))))

noncomputable def p12237 :=
nat_lit 32947218924242694200125604984224833798445644825384144574356293080216569586982051535310023664765125

noncomputable def p12238 :=
nat_lit 4271974071841820164790043412339104229205409044713305539894083215644439451561281100045924173873152

noncomputable def p12239 :=
nat_lit
  5239954235318689729485365634361863048596479146285116688895637187425697345169991849046186137732629533437651851220934203952033

noncomputable def p12240 :=
nat_lit
  4173702698141214800803531440441153900989545943276081002689440724048427175245565132800000000000000000000000000000000000000000000000000

noncomputable def p12241 :=
nat_lit
  31137008363398331265428332037436874008823126219405845672990501935810331988267649609519656063577384921984614457836668761787743067938656885875

noncomputable def p12242 :=
nat_lit
  4823096580324602579103163838896125478430016257136558738355862145782754356639516784842424732157000289580373465483115713235482310334066627065534967389073982278202989514777626234773889057108801

noncomputable def p12243 :=
nat_lit
  145277517464015712500201970701587634323679483972389355757211209644134340532540621056157597318268306675401999232211410105927844672824987846117727672240007866063254263936912995064985833923787630444881331767949735956128095715115340398592000

noncomputable def p12244 :=
@p12236 p12237 p12238 p12239
  p12240 p12241 p12180 p12242
  p12182 p12243 p12228 p12180

noncomputable def p12245 :=
@Enclosure.Real.IsNear.subLit_tt_n
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p12168
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p12089 (Enclosure.sfrac false 1 16)))))

noncomputable def p12246 :=
@p12245
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p12170
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 4 1) Real.pi))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p12089 (Enclosure.sfrac false 1 16)))))

noncomputable def p12247 :=
nat_lit 80224098532954959610988525757754658688929332002392232024333507706499129356172904274272057402493125

noncomputable def p12248 :=
nat_lit
  1353821405761478367802495382544859132452546711358995957431908053030070961108881032470663907768058380723151181780934203952033

noncomputable def p12249 :=
nat_lit 67838995244807942241401094777367746257557651228871790375

noncomputable def p12250 :=
nat_lit 4568127187689533437466114577755188444018162100327194870052506015052337471

noncomputable def p12251 :=
nat_lit 4906163943676737091137858019982639531315691520000000000000000000000000000000000000

noncomputable def p12252 :=
nat_lit
  201965864341336626078685560113156355927218816509964565622331709995577015098913595076155344718820959440713144299618017719746755202423727832730485915648000

noncomputable def p12253 :=
@p12246 p12247 p12238 p12248
  p12240 p12249 p2977 p12250
  p12251 p12252 p12237 p12238

noncomputable def p12254 :=
nat_lit 2294082418008100114974614017964039330261237839591867814770382916407112284780605376125

noncomputable def p12255 :=
@Enclosure.Real.IsNear.mulLit_ft p12168
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p12089 (Enclosure.sfrac false 1 16))))
  p12254

noncomputable def p12256 :=
nat_lit 4302206520211870350900071053143772840130276746298626285551841110196487895345833367729309339115974480107

noncomputable def p12257 :=
nat_lit
  27606985387162255149739023449108101809804435888681546220650096895197184000000000000000000000000000000000000000000

noncomputable def p12258 :=
@p12255 p12222 p12256 p12257
  34970015856105 35184372088832 4068320057 453548546457600000000
  p12247 p12238 p12248 p12240

noncomputable def p12259 :=
@Enclosure.Real.IsNear.mulLit_ff p12167
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p12260 :=
nat_lit 173942621462808933238360593902880448763777321397692544025

noncomputable def p12261 :=
nat_lit 24519928653854221733733552434404946937899825954937634816

noncomputable def p12262 :=
nat_lit 35630090781209063828027525923099216987070797640215353496305293399

noncomputable def p12263 :=
nat_lit 913438523331814323877303020447676887284957839360000000000000000000000000000

noncomputable def p12264 :=
nat_lit 13188730851101971488679907845

noncomputable def p12265 :=
nat_lit 4951760157141521099596496896

noncomputable def p12266 :=
nat_lit 221311441543956844835549843

noncomputable def p12267 :=
nat_lit 30223145490365729367654400000000000000

noncomputable def p12268 :=
@p12259 p12260 p12261 p12262
  p12263 p12264 p12265 p12266
  p12267 p12254 p12222 p12256

noncomputable def p12269 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p12270 :=
@p12269
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p12271 :=
@p12270 p12264 p12265 p12266
  p12267 p12264 p12265 p12266
  p12267 p12260 p12261 p12262

noncomputable def p12272 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
        (Enclosure.sfrac false 12 1)))
    (Enclosure.sfrac false 1 1))
  884279719003555

noncomputable def p12273 :=
@p12272 140737488355328 1 500000000000000 14914659431479
  35184372088832 41 35184372088832 p12264 p12265
  p12266 p12267

noncomputable def p12274 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 2 1)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
      (Enclosure.sfrac false 12 1)))
  (Enclosure.sfrac false 1 1) 50099031520311 35184372088832

noncomputable def p12275 :=
@p12274 41 35184372088832 1 1 0 1
  14914659431479 14914659431479 35184372088832 41 35184372088832

noncomputable def p12276 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 2 1)
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
    (Enclosure.sfrac false 12 1))
  2 1 0 1

noncomputable def p12277 :=
@p12276 50099031520311 70368744177664 41 70368744177664
  50099031520311 35184372088832 41 35184372088832
  (Enclosure.Real.IsNear.const false 2 1)
  (@p12192 1 50099031520311 50099031520311 70368744177664
    41 70368744177664 (p12197 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p12278 :=
@p12271 p12263
  (p12273 d197
    (p12275 (p12277 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (p12273 d197
    (p12275 (p12277 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))

noncomputable def p12279 :=
@p12268 p12257 (p12278 (Eq.refl true))
  (p12273 d197
    (p12275 (p12277 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p12280 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p12089 (Enclosure.sfrac false 1 16))))
  true

noncomputable def p12281 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p12089 (Enclosure.sfrac false 1 16)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Neg.neg.{0} Real Real.instNeg (@Nat.cast.{0} Real Real.instNatCast 59153266790181))
    (@Nat.cast.{0} Real Real.instNatCast 35184372088832))
  true

noncomputable def p12282 :=
nat_lit 1171651158625531306035489069653881491217645

noncomputable def p12283 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p12089 (Enclosure.sfrac false 1 16)))
  true p12282

noncomputable def p12284 :=
nat_lit 696898287454081973172991196020261297061888

noncomputable def p12285 :=
nat_lit 188731459071030772472444319271562123493257

noncomputable def p12286 :=
nat_lit 21267647932558653966460912964485513216000000000000000

noncomputable def p12287 :=
nat_lit 1324977983149719856127777839

noncomputable def p12288 :=
nat_lit 1015492973328374787402996783

noncomputable def p12289 :=
@p12130 (Enclosure.sfrac false 1 16) p12288
  p12265 6993239095951407 p12265 1 16 0

noncomputable def p12290 :=
nat_lit 21199647730395517698044445424

noncomputable def p12291 :=
nat_lit 2509912959273115108005536721

noncomputable def p12292 :=
@Enclosure.Real.IsNear.subLit_ff_n
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
      (Enclosure.sfrac false 12 1))
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
      (Enclosure.sfrac false 12 1)))
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
    (Enclosure.sfrac false 12 1))
  p12291

noncomputable def p12293 :=
nat_lit 71458965254359776964228283684916572454912

noncomputable def p12294 :=
@p12292 p12265 4108120584667183 p12265
  50099031520311 70368744177664 41 70368744177664 p12293
  p12288 p12265 6993239095951407

noncomputable def p12295 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
    (Enclosure.sfrac false 12 1))
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
    (Enclosure.sfrac false 12 1))
  50099031520311 70368744177664 41

noncomputable def p12296 :=
@p12295 70368744177664 50099031520311 70368744177664 41
  70368744177664 p12291 p12265 4108120584667183
  p12265
  (@p12192 1 50099031520311 50099031520311 70368744177664
    41 70368744177664 (p12197 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p12297 :=
p12296
  (@p12192 1 50099031520311 50099031520311 70368744177664
    41 70368744177664 (p12197 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p12298 :=
@p12294 p12265 (p12297 (Eq.refl true))
  (@p12192 1 50099031520311 50099031520311 70368744177664
    41 70368744177664 (p12197 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p12299 :=
@p12129 500000000000000 p12287 p12265
  6993239095951407 p12265 p12282 p12284
  p12285 p12286 d197
  (@p12289 1 p12290 p12287 p12265
    6993239095951407 p12265
    (p12298 (Eq.refl true) (Eq.refl true))
    (Enclosure.Real.IsNear.const false 1 16) (Eq.refl true)
    (Eq.refl true))

noncomputable def p12300 :=
@p12281 59153266790181 35184372088832 313 35184372088832
  true 34970015856105 35184372088832 1 13516800000000
  (@p12283 p12284 p12285 p12286
    59153266790181 35184372088832 313 35184372088832
    (p12299 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_true_div 59153266790181 35184372088832)

noncomputable def p12301 :=
nat_lit
  130962299522360871997777654796909327420284356143731394954563746495093967920246487657412228569634494481398756659486434902478343301814992137999781995670862398380044662602412033864666975094495380846889937460933367860386592260616395201

noncomputable def p12302 :=
nat_lit
  1961848167734627781231279786490110123562935172081945904365228885641390576241135963171198423910219637317516664724571812977087383204305824875125189264690483141925255757791594586255777610605882706058377906934724181744813017762103296000

noncomputable def p12303 :=
nat_lit
  22472932255649732233471921681625430449724246718499313543559851901940699580465535214004198951647799594143816115254636445769515621190084761308993279968786314429025732795520344907644956446756402077645992229102321153004050881

noncomputable def p12304 :=
nat_lit
  1064669141244215360628916813200397806713903552683402803407931116313965552434061670959888745691429406880380590842941833096735386030530451407755283831945596089697011061774701736074499377068881809429035350539794466523308862568850037185

noncomputable def p12305 :=
nat_lit
  111825345560873783530182947829936277043087304808670916548818046481559262845744749900758310162882519327098449889300593339693980842645432017882135788087357539089739578194120891416579323804535314245327540695279278359454342012439887872000

noncomputable def p12306 :=
BSN.sin_dyadic_bound_f 59153266790181 35184372088832 5 4
  35184372088832 13516800000000 p12301 p12302
  p12303 p12304 p12305

noncomputable def p12307 :=
@BSN.binarySplit_of_base4 (BSN.sinEvenP 59153266790181) (BSN.sinEvenQ 35184372088832) 0
  4 p12301 p12302 p12303 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p12308 :=
p12306 p12303 34970015856105 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p12307 (Eq.refl true))

noncomputable def p12309 :=
@BSN.binarySplit_of_base4 (BSN.sinOddP 59153266790181) (BSN.sinOddQ 35184372088832) 0
  4 p12304 p12305 p12303 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p12310 :=
p12300
  (BSN.sin_neg_of_bound 59153266790181 35184372088832 false 34970015856105
    35184372088832 1 13516800000000
    (p12308 (p12309 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p12311 :=
p12258 p12279
  (@p12280 34970015856105 35184372088832 4265942772088832
    p12185 34970015856105 35184372088832 4068320057
    453548546457600000000 (p12310 (Eq.refl true))
    (Eq.refl true))

noncomputable def p12312 :=
nat_lit 34987581633077904379594644296294257882166925

noncomputable def p12313 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p12170
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 4 1) Real.pi))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p12089 (Enclosure.sfrac false 1 16))))
  p12312

noncomputable def p12314 :=
nat_lit 348449143727040986586495598010130648530944

noncomputable def p12315 :=
nat_lit 17919056159164526463580649341209116016634325745966543

noncomputable def p12316 :=
nat_lit 64903710731685345356631204115251200000000000000000000000000000

noncomputable def p12317 :=
@p12313 p12314 p12315 p12316
  1938944964995 17592186044416 4068320057 453548546457600000000
  p12249 p2977 p12250 p12251

noncomputable def p12318 :=
nat_lit 39566192553305914466039723535

noncomputable def p12319 :=
nat_lit 663934324631870534506649529

noncomputable def p12320 :=
@Enclosure.Real.IsNear.mulLit_ff p12170
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 4 1) Real.pi)
  p12318 p12265 p12319 p12267

noncomputable def p12321 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 3 1)
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p12322 :=
@p12321 3 1 0 1 p12264
  p12265 p12266 p12267 p12318
  p12265 p12319

noncomputable def p12323 :=
@p12322 p12267 (Enclosure.Real.IsNear.const false 3 1)
  (p12273 d197
    (p12275 (p12277 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p12324 :=
@p12320 884279719003555 70368744177664 1 250000000000000
  p12312 p12314 p12315 p12316
  p12323 d199 (Eq.refl true)

noncomputable def p12325 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p12089 (Enclosure.sfrac false 1 16)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Neg.neg.{0} Real Real.instNeg (@Nat.cast.{0} Real Real.instNatCast 59153266790181))
    (@Nat.cast.{0} Real Real.instNatCast 35184372088832))
  true

noncomputable def p12326 :=
@p12325 59153266790181 35184372088832 313 35184372088832
  true 3877889929990 35184372088832 1 13516800000000
  (@p12283 p12284 p12285 p12286
    59153266790181 35184372088832 313 35184372088832
    (p12299 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_true_div 59153266790181 35184372088832)

noncomputable def p12327 :=
nat_lit
  38599596925953355681954798557187823612580266652797389267077474928685750644925682656666172663937698464350894929917493833876691738356386171870631342017382252666706338806754692451408126337192789523501936258611075160876956465555085761

noncomputable def p12328 :=
nat_lit
  115402833396154575366545869793535889621349127769526229668542875625964151543596233127717554347659978665736274395563047822181610776723872051477952309687675478936779750458329093309163388859169570944610465113807304808518412809535488000

noncomputable def p12329 :=
nat_lit
  392472513737281217088534996796810756479344794044669079316808650885153275322275272012825831921820336148987047229998254897954196787010184712968464164968054251208536224823525826582877679349068986193072813569405218565183765963736390081

noncomputable def p12330 :=
nat_lit
  17656633509611650031081518078410991112066416548737513139287059970772515186170223668540785815191976735857649982521146316793786448838752423876126703382214348277327301820124351276301998495452944354525401162412517635703317159858929664000

noncomputable def p12331 :=
BSN.cos_dyadic_bound_t 59153266790181 35184372088832 5 4
  35184372088832 13516800000000 p12327 p12328
  p12303 p12329 p12330

noncomputable def p12332 :=
@BSN.binarySplit_of_base4 (BSN.cosEvenP 59153266790181) (BSN.cosEvenQ 35184372088832) 0
  4 p12327 p12328 p12303 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p12333 :=
p12331 p12303 3877889929990 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p12332 (Eq.refl true))

noncomputable def p12334 :=
@BSN.binarySplit_of_base4 (BSN.cosOddP 59153266790181) (BSN.cosOddQ 35184372088832) 0
  4 p12329 p12330 p12303 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p12335 :=
p12326
  (BSN.cos_neg_of_bound 59153266790181 35184372088832 true 3877889929990
    35184372088832 1 13516800000000
    (p12333 (p12334 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p12336 :=
p12317 p12324
  (@p12124 3877889929990 35184372088832 4265942772088832
    p12185 1938944964995 17592186044416 4068320057
    453548546457600000000 (p12335 (Eq.refl true))
    (Eq.refl true))

noncomputable def p12337 :=
nat_lit 90683697789433838312785270695

noncomputable def p12338 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 3 1) p12172)
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
      (Enclosure.sfrac false 12 1)))
  p12337

noncomputable def p12339 :=
nat_lit 45784179377121979064790353966946119

noncomputable def p12340 :=
nat_lit 649325391394576216883200000000000000000000000

noncomputable def p12341 :=
nat_lit 343358388799914062592954419892347996060073279018041773812354597007672621075892419181870105478448624168558538325

noncomputable def p12342 :=
nat_lit 75153362648762663292463379097258784876021841565066235862633311089030688803667470190838367948312598497021919232

noncomputable def p12343 :=
nat_lit
  405498593938155329960380946548693073510095791063174563216835477149118843156883963174528454450034446514061786040225523403707556085220628454707929

noncomputable def p12344 :=
nat_lit
  5552731923458459608726120880686863016672265076673251634374047617209715732449282367344848706469888000000000000000000000000000000000000000000000000000000

noncomputable def p12345 :=
@p12338 p12265 p12339 p12340
  p12341 p12342 p12343 p12344
  p12241 p12180 p12242 p12182

noncomputable def p12346 :=
nat_lit 30227899263144612770928423565

noncomputable def p12347 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 3 1) p12172
  3 1 0 1 p12346 p12265

noncomputable def p12348 :=
nat_lit 1947976174183728650649600000000000000000000000

noncomputable def p12349 :=
@Enclosure.Real.IsNear.neg
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
          (Enclosure.sfrac false 12 1)))))

noncomputable def p12350 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
        (Enclosure.sfrac false 12 1))))
  884279719003555

noncomputable def p12351 :=
@p12350 140737488355328 1 500000000000000 34183639648783
  35184372088832 1696445057 453548546457600000000 p12346
  p12265 p12339 p12348

noncomputable def p12352 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
        (Enclosure.sfrac false 12 1))))
  true

noncomputable def p12353 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
      (Enclosure.sfrac false 12 1)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 314781498752345)
    (@Nat.cast.{0} Real Real.instNatCast 70368744177664))
  false

noncomputable def p12354 :=
@p12353 314781498752345 70368744177664 129 35184372088832
  true 68367279297566 70368744177664 1 13516800000000
  (@p12188 p12189 p12190 p12191
    314781498752345 70368744177664 129 35184372088832
    (p12198 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div 314781498752345 70368744177664)

noncomputable def p12355 :=
BSN.sin_reduce2
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 314781498752345)
    (@Nat.cast.{0} Real Real.instNatCast 70368744177664))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast p12200)
    (@Nat.cast.{0} Real Real.instNatCast p12201))
  226375608064910080 72057594037927936 false

noncomputable def p12356 :=
nat_lit
  323108589839002279950680674091537848273421672605306710986812194820039382302601540409132777919485638106672008073293467623008783662720934051014408290677158349605982353059397155122773856027670385909250668725962268466582357392082560116480828664062433001777422824792369905423121121280000000000

noncomputable def p12357 :=
nat_lit
  12314720538252212013175536584546949912589922018805340084673386748512714874007374005243903479319278300245823356305175174303539820705499876134073153122420792581317882717422223006813658783748121083660254535082634382113709149488299688196491642633853971843408327376193589307780822967796105216000

noncomputable def p12358 :=
nat_lit
  2629336784574972716186181635916362852347160812690191992350484812492302575635843684314037281152610222701421228604464485143830071307206018189411543528513907061690007144638831691870370795981192544057597338589729575742179339027156498083951312607622599569565879772365812946328386273280000000000

noncomputable def p12359 :=
nat_lit
  701939070680376084751005585319176145017625555071904384826383044665224747818420318298902498321198863114011931309394984935301769780213492939642169727977985177135119314893066711388378550673642901768634508499710159780481421520833082227200023630129676395074274660443034590543506909164377997312000

noncomputable def p12360 :=
BSN.sin_dyadic_bound_f 191921293314982400 144115188075855872 5 4
  70368744177664 27060000000001 p12356 p12357
  p12206 p12358 p12359

noncomputable def p12361 :=
@BSN.binarySplit_of_base4 (BSN.sinEvenP 191921293314982400) (BSN.sinEvenQ 144115188075855872)
  0 4 p12356 p12357 p12206
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p12362 :=
p12360 p12206 68367279297566 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p12361 (Eq.refl true))

noncomputable def p12363 :=
@BSN.binarySplit_of_base4 (BSN.sinOddP 191921293314982400) (BSN.sinOddQ 144115188075855872)
  0 4 p12358 p12359 p12206
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p12364 :=
@BSN.sin_arg_round false 68367279297566 70368744177664 p12200
  p12201 191921293314982400 144115188075855872 27060000000001
  27033600000000
  (p12362 (p12363 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p12365 :=
p12355 68367279297566 70368744177664 0 1000000000000000
  27033600000000 13516800000000 p12203 BSN.pi_near_15 p12364
  (Eq.refl true) (Eq.refl true)

noncomputable def p12366 :=
p12351 d197
  (@p12352 68367279297566 70368744177664 1778851572088832
    p12185 34183639648783 35184372088832 1696445057
    453548546457600000000
    (p12354 (p12365 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p12367 :=
@Neg.neg.{0} Real Real.instNeg
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p12167
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p12089 (Enclosure.sfrac false 1 16)))))

noncomputable def p12368 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p12367
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 4 1) Real.pi)
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p12089 (Enclosure.sfrac false 1 16)))))

noncomputable def p12369 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p12368
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) p12172)
    (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
        (Enclosure.sfrac false 12 1))))

noncomputable def p12370 :=
@Enclosure.Real.IsNear.of_eq
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
      (Enclosure.sfrac false 12 1)))
  (p12088
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p12369
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p12174
        (Zeta.RiemannSiegel.correction
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
            (Enclosure.sfrac false 12 1))))))

noncomputable def p12371 :=
@p12092
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p12369
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p12174
      (Zeta.RiemannSiegel.correction
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
          (Enclosure.sfrac false 12 1)))))
  297160440153807

noncomputable def p12372 :=
nat_lit 1155464666232811839535855880711633791548629489313320837556777944418097091856433379135889207640475

noncomputable def p12373 :=
nat_lit 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288

noncomputable def p12374 :=
nat_lit
  4089687435923166337445777665691374770849926459783128597045720346286555529839365980393248125863288139246504379672883222256550728581

noncomputable def p12375 :=
nat_lit
  236727199910197026983075298887521697821750808970190219371291716067121728845959397376000000000000000000000000000000000000000000000000000000

noncomputable def p12376 :=
@p12371 70368744177664 4695 70368744177664 p12372
  p12373 p12374 p12375 p12341
  p12342 p12343 p12344

noncomputable def p12377 :=
nat_lit 3491549822526493334923968856184776892524200257533980075584620546337874101170917802353098886823525

noncomputable def p12378 :=
@Enclosure.Real.IsNear.subLit_ff_n p12369
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p12174
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
        (Enclosure.sfrac false 12 1))))
  p12377 p12373

noncomputable def p12379 :=
nat_lit
  3973312934610021587877381402547092625873572082197419729090351199592114290589382295980634318573898679057241960723514198563750728581

noncomputable def p12380 :=
nat_lit 7507656819052181235774904491106066933688140859830839532050443110037625

noncomputable def p12381 :=
nat_lit 1725436586697640946858688965569256363112777243042596638790631055949824

noncomputable def p12382 :=
nat_lit 7292631157709105868795522368553384781925570314036330126446570351514179438921287459050189508629

noncomputable def p12383 :=
nat_lit 14834556835581804148908799222814992897429394702737269063680000000000000000000000000000000000000000000000

noncomputable def p12384 :=
nat_lit
  1993681009754471805401544862376178618447029935687080309298122849102465937536655154992848589438836057794291527790698673561064677011599014355261198227319640709031526400

noncomputable def p12385 :=
@p12378 p12379 p12375 p12380
  p12381 p12382 p12383 p12384
  p12372 p12373 p12374 p12375

noncomputable def p12386 :=
@Enclosure.Real.IsNear.subLit_ff_p p12368
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) p12172)
    (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
        (Enclosure.sfrac false 12 1))))

noncomputable def p12387 :=
nat_lit 5724859656047570196111485012521133503903516676179108110811564889225675

noncomputable def p12388 :=
nat_lit 431359146674410236714672241392314090778194310760649159697657763987456

noncomputable def p12389 :=
nat_lit 37421780832281972417114950855326829153712026400990516432027505577689930458893912850309

noncomputable def p12390 :=
nat_lit 207144357267760465206581050965852991731377729667313138925568000000000000000000000000000000000000

noncomputable def p12391 :=
nat_lit 10682516152495141978738532624018293677937734494169171063600376471059504708634846338818163103678875

noncomputable def p12392 :=
nat_lit
  1310182282878453118060987777606702716660217302159971722486128404313384188176265545589950280713686181644067000411838066187916909527

noncomputable def p12393 :=
nat_lit
  78909066636732342327691766295840565940583602990063406457097238689040576281986465792000000000000000000000000000000000000000000000000000000

noncomputable def p12394 :=
nat_lit
  1506111952016216669638659404590908524488921579390444891685747712588782777253542059418107524246274649978541732893637984984541060981814021541269387604947241661785702400

noncomputable def p12395 :=
@p12386 p12387 p12388 p12389
  p12390 p12391 p12373 p12392
  p12393 p12394 p12377 p12373

noncomputable def p12396 :=
@Enclosure.Real.IsNear.subLit_ft p12367
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 4 1) Real.pi)
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p12089 (Enclosure.sfrac false 1 16)))))

noncomputable def p12397 :=
nat_lit 337265170083344602752226373736207942157952109461423834248326121404875

noncomputable def p12398 :=
nat_lit 4690544574916772954850328945818225527943782869368582647172366320781947806297970950103

noncomputable def p12399 :=
nat_lit 69048119089253488402193683655284330577125909889104379641856000000000000000000000000000000000000

noncomputable def p12400 :=
nat_lit 30923275794786392240863453275

noncomputable def p12401 :=
nat_lit 109791864063091341891807890770071119

noncomputable def p12402 :=
nat_lit 973988087091864325324800000000000000000000000

noncomputable def p12403 :=
nat_lit 14174065975021635313662501480203070570461934751703151139184997017397378809805764141171261990502400

noncomputable def p12404 :=
@p12396 p12397 p12388 p12398
  p12399 p12400 p2333 p12401
  p12402 p12403 p12387 p12388

noncomputable def p12405 :=
@Enclosure.Real.IsNear.neg
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p12167
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p12089 (Enclosure.sfrac false 1 16)))))

noncomputable def p12406 :=
@Enclosure.Real.IsNear.mulLit_ft p12167
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p12089 (Enclosure.sfrac false 1 16))))
  p12260

noncomputable def p12407 :=
@p12406 p12261 p12262 p12263
  1938944964995 17592186044416 4068320057 453548546457600000000
  p12397 p12388 p12398 p12399

noncomputable def p12408 :=
p12407 (p12278 (Eq.refl true))
  (@p12124 3877889929990 35184372088832 4265942772088832
    p12185 1938944964995 17592186044416 4068320057
    453548546457600000000 (p12335 (Eq.refl true))
    (Eq.refl true))

noncomputable def p12409 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 4 1) Real.pi)
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p12089 (Enclosure.sfrac false 1 16))))
  884279719003555

noncomputable def p12410 :=
@p12409 70368744177664 1 250000000000000 34970015856105
  35184372088832 4068320057 453548546457600000000 p12400
  p2333 p12401 p12402

noncomputable def p12411 :=
p12410 d199
  (@p12280 34970015856105 35184372088832 4265942772088832
    p12185 34970015856105 35184372088832 4068320057
    453548546457600000000 (p12310 (Eq.refl true))
    (Eq.refl true))

noncomputable def p12412 :=
@p12395 p12379 p12375
  (@p12404 p12389 p12390
    (@p12405 true p12397 p12388 p12398
      p12399 (p12408 (Eq.refl true)))
    (p12411 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p12413 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 2 1) p12172)
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
      (Enclosure.sfrac false 12 1)))
  p12346

noncomputable def p12414 :=
nat_lit 353399224322538590619137818491783100489459409612620217670154198847175

noncomputable def p12415 :=
nat_lit 329771014451221411744582993472042258885862831297131313860547651520695355353341787549

noncomputable def p12416 :=
nat_lit 243049379194172279175721766466600843631483202809647416339333120000000000000000000000000000000

noncomputable def p12417 :=
@p12413 p2333 p12339 p12402
  p12414 p12388 p12415 p12416
  p12391 p12373 p12392 p12393

noncomputable def p12418 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 2 1) p12172
  2 1 0 1 p12346 p12265

noncomputable def p12419 :=
@Neg.neg.{0} Real Real.instNeg
  (p12166
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p12089 (Enclosure.sfrac false 1 16)))))

noncomputable def p12420 :=
@Enclosure.Real.IsNear.of_eq
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
      (Enclosure.sfrac false 12 1)))
  (p12088
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p12419
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p12172
        (Zeta.RiemannSiegel.correction
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
            (Enclosure.sfrac false 12 1))))))

noncomputable def p12421 :=
@p12092
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p12419
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p12172
      (Zeta.RiemannSiegel.correction
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
          (Enclosure.sfrac false 12 1)))))
  297160440153807

noncomputable def p12422 :=
nat_lit 1189253940193462527649380003279086914547282567446886025

noncomputable def p12423 :=
nat_lit 1099153587534172983470864959558653724002794347542877845931442075975587

noncomputable def p12424 :=
nat_lit 3453939416348422912161052046067778230046246830080000000000000000000000000000000

noncomputable def p12425 :=
@p12421 70368744177664 4695 70368744177664 p12422
  p2977 p12423 p12424 p12414
  p12388 p12415 p12416

noncomputable def p12426 :=
nat_lit 461210126984937134771362008854580180643725

noncomputable def p12427 :=
nat_lit 174224571863520493293247799005065324265472

noncomputable def p12428 :=
@Enclosure.Real.IsNear.subLit_ff_n p12419
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p12172
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
        (Enclosure.sfrac false 12 1))))
  p12426 p12427

noncomputable def p12429 :=
nat_lit 142418019867658928503006249843796397098039617017

noncomputable def p12430 :=
nat_lit 4569221235510648313106836769713684480000000000000000000000

noncomputable def p12431 :=
nat_lit 17416642659168947074385051425495559864713369040090265225

noncomputable def p12432 :=
nat_lit 991497777700262474574369681344416652415501482442010952549810075975587

noncomputable def p12433 :=
nat_lit 207197258567210814971086247159930739797840175640577570120118586834526762137475503252956826828800

noncomputable def p12434 :=
@p12428 p12429 p12430 p12431
  p2977 p12432 p12424 p12433
  p12422 p2977 p12423 p12424

noncomputable def p12435 :=
@Enclosure.Real.IsNear.neg
  (p12166
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p12089 (Enclosure.sfrac false 1 16)))))

noncomputable def p12436 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p12437 :=
@p12436
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p12089 (Enclosure.sfrac false 1 16))))
  p12264

noncomputable def p12438 :=
@p12437 p12265 p12266 p12267
  34970015856105 35184372088832 4068320057 453548546457600000000
  p12426 p12427 p12429 p12430

noncomputable def p12439 :=
p12438
  (p12273 d197
    (p12275 (p12277 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (@p12280 34970015856105 35184372088832 4265942772088832
    p12185 34970015856105 35184372088832 4068320057
    453548546457600000000 (p12310 (Eq.refl true))
    (Eq.refl true))

noncomputable def p12440 :=
@Enclosure.Real.IsNear.mulLit_ff p12172
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
      (Enclosure.sfrac false 12 1)))
  p12346 p12265 p12339

noncomputable def p12441 :=
nat_lit 576177739231922106030985965

noncomputable def p12442 :=
nat_lit 83113650098505755761049600000000

noncomputable def p12443 :=
@p12092
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p12089 (Enclosure.sfrac false 1 16))))
  297160440153807

noncomputable def p12444 :=
@p12443 70368744177664 4695 70368744177664 1938944964995
  17592186044416 4068320057 453548546457600000000 p12441
  p2445 3759477691795941600471 p12442

noncomputable def p12445 :=
p12444
  (p12184
    (@Enclosure.Real.IsNear.neg p12096 false 297160440153807 70368744177664
      4695 70368744177664 (p12217 (Eq.refl true))))
  (@p12124 3877889929990 35184372088832 4265942772088832
    p12185 1938944964995 17592186044416 4068320057
    453548546457600000000 (p12335 (Eq.refl true))
    (Eq.refl true))

noncomputable def p12446 :=
@p12440 p12348 p12441 p2445
  3759477691795941600471 p12442 p12431 p2977
  p12432 p12424
  (@p12349 true p12346 p12265 p12339
    p12348 (p12366 (Eq.refl true)))
  (@p12090 false p12441 p2445
    3759477691795941600471 p12442
    (BSN.correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
        (Enclosure.sfrac false 12 1))
      (p12091 (Eq.refl true) (Eq.refl true)
        (p11864 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p12445 (Eq.refl true)))

noncomputable def p12447 :=
p12425
  (p12184
    (@Enclosure.Real.IsNear.neg p12096 false 297160440153807 70368744177664
      4695 70368744177664 (p12217 (Eq.refl true))))
  (p12434
    (@p12435 true p12426 p12427 p12429
      p12430 (p12439 (Eq.refl true)))
    (p12446 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p12448 :=
p12417
  (@p12418 p12339 p12348 p12346
    p2333 p12339 p12402
    (Enclosure.Real.IsNear.const false 2 1)
    (@p12349 true p12346 p12265 p12339
      p12348 (p12366 (Eq.refl true)))
    (Eq.refl true))
  (@p12420 false p12414 p12388 p12415
    p12416
    (BSN.deriv_correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
        (Enclosure.sfrac false 12 1))
      (p12091 (Eq.refl true) (Eq.refl true)
        (p11864 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p12447 (Eq.refl true)))

noncomputable def p12449 :=
nat_lit 13030105656390539048816927511692687987428925

noncomputable def p12450 :=
nat_lit 1393796574908163946345982392040522594123776

noncomputable def p12451 :=
nat_lit 1235482964539436314228680944888742164933882461476549729889073

noncomputable def p12452 :=
@Enclosure.Real.IsNear.mulLit_ff p12174
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
      (Enclosure.sfrac false 12 1)))
  p12449 p12450 p12451

noncomputable def p12453 :=
nat_lit 8366493961506314049878241155481600000000000000000000000000000000000000

noncomputable def p12454 :=
@Enclosure.Real.IsNear.neg
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 4 1)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
          (Enclosure.sfrac false 12 1)))))

noncomputable def p12455 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 4 1)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
        (Enclosure.sfrac false 12 1))))
  p1068

noncomputable def p12456 :=
@p12455 p1070 p1071 p1072
  16663591407317 70368744177664 1696445057 453548546457600000000
  p12449 p12450 p12451 p12453

noncomputable def p12457 :=
p12456 d201
  (@p12100 16663591407317 70368744177664 1778851572088832
    p12185 16663591407317 70368744177664 1696445057
    453548546457600000000
    (p12199 (p12214 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p12458 :=
@p12452 p12453 p12441 p2445
  3759477691795941600471 p12442 p12380 p12381
  p12382 p12383
  (@p12454 true p12449 p12450 p12451
    p12453 (p12457 (Eq.refl true)))
  (@p12090 false p12441 p2445
    3759477691795941600471 p12442
    (BSN.correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
        (Enclosure.sfrac false 12 1))
      (p12091 (Eq.refl true) (Eq.refl true)
        (p11864 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p12445 (Eq.refl true)))

noncomputable def p12459 :=
p12376
  (p12184
    (@Enclosure.Real.IsNear.neg p12096 false 297160440153807 70368744177664
      4695 70368744177664 (p12217 (Eq.refl true))))
  (p12385
    (p12412 (p12448 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true))
    (p12458 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p12460 :=
p12345
  (@p12347 p12339 p12348 p12337
    p12265 p12339 p12340
    (Enclosure.Real.IsNear.const false 3 1)
    (@p12349 true p12346 p12265 p12339
      p12348 (p12366 (Eq.refl true)))
    (Eq.refl true))
  (@p12370 false p12341 p12342 p12343
    p12344
    (BSN.iteratedDeriv_two_correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
        (Enclosure.sfrac false 12 1))
      (p12091 (Eq.refl true) (Eq.refl true)
        (p11864 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p12459 (Eq.refl true)))

noncomputable def p12461 :=
@p12244 p12229 p12182
  (@p12253 p12239 p12240
    (p12311 (Eq.refl true)) (p12336 (Eq.refl true))
    (Eq.refl true) (Eq.refl true))
  (p12460 (Eq.refl true)) (Eq.refl true) (Eq.refl true)

noncomputable def p12462 :=
nat_lit 39090316969171617146450782535078063962286775

noncomputable def p12463 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 3 1) p12174)
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
      (Enclosure.sfrac false 12 1)))
  p12462

noncomputable def p12464 :=
nat_lit 2788831320502104683292747051827200000000000000000000000000000000000000

noncomputable def p12465 :=
@p12463 p12450 p12451 p12464
  p12414 p12388 p12415 p12416
  p12230 p12231 p12232 p12233

noncomputable def p12466 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 3 1) p12174
  3 1 0 1 p12449 p12450

noncomputable def p12467 :=
p12465
  (@p12466 p12451 p12453 p12462
    p12450 p12451 p12464
    (Enclosure.Real.IsNear.const false 3 1)
    (@p12454 true p12449 p12450 p12451
      p12453 (p12457 (Eq.refl true)))
    (Eq.refl true))
  (@p12420 false p12414 p12388 p12415
    p12416
    (BSN.deriv_correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
        (Enclosure.sfrac false 12 1))
      (p12091 (Eq.refl true) (Eq.refl true)
        (p11864 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p12447 (Eq.refl true)))

noncomputable def p12468 :=
nat_lit 23636724613672063048793203128112905493807237354941075059125

noncomputable def p12469 :=
nat_lit 98079714615416886934934209737619787751599303819750539264

noncomputable def p12470 :=
nat_lit 33347762286468396114982742738505400978177311469991462092466988447255543160884181997591

noncomputable def p12471 :=
@Enclosure.Real.IsNear.mulLit_tf p12176
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
      (Enclosure.sfrac false 12 1)))
  p12468 p12469 p12470

noncomputable def p12472 :=
nat_lit 35933817946851101741732358544794723129753600000000000000000000000000000000000000000000000000000

noncomputable def p12473 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 8 1)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi) Real.pi))
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
        (Enclosure.sfrac false 12 1))))

noncomputable def p12474 :=
@p12473 p1059 p1061 p1062
  p1063 34183639648783 35184372088832 1696445057
  453548546457600000000 p12468 p12469 p12470

noncomputable def p12475 :=
@p12474 p12472 d202
  (@p12352 68367279297566 70368744177664 1778851572088832
    p12185 34183639648783 35184372088832 1696445057
    453548546457600000000
    (p12354 (p12365 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p12476 :=
@p12471 p12472 p12441 p2445
  3759477691795941600471 p12442 p12221 p12222
  p12223 p12224 (p12475 (Eq.refl true))
  (@p12090 false p12441 p2445
    3759477691795941600471 p12442
    (BSN.correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
        (Enclosure.sfrac false 12 1))
      (p12091 (Eq.refl true) (Eq.refl true)
        (p11864 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p12445 (Eq.refl true)))

noncomputable def p12477 :=
p12183
  (p12184
    (@Enclosure.Real.IsNear.neg p12096 false 297160440153807 70368744177664
      4695 70368744177664 (p12217 (Eq.refl true))))
  (p12226
    (@p12235 p12220 p12182 p12461
      (p12467 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true))
    (p12476 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p12478 :=
@p12165 p12157
  (@p12177 false p12161 p12162 p12163
    p12164
    (BSN.iteratedDeriv_three_correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
        (Enclosure.sfrac false 12 1))
      (p12091 (Eq.refl true) (Eq.refl true)
        (p11864 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p12477 (Eq.refl true)))

noncomputable def p12479 :=
@p12155 p12156 p12157 84467121 1073741824
  1 8589934592 p12083 p9769 p12084
  p12085
  (@p12159 p12154 p12156 p12157
    (BSN.correctionLinear_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p11861
        (Enclosure.sfrac false 12 1)))
    (@Enclosure.Real.IsNear.neg p12158 false p12153 p12154
      p12156 p12157
      (p12478 d203 (Eq.refl true))))

noncomputable def p12480 :=
@Enclosure.Real.IsNear.recentre' (@Inv.inv.{0} Real Real.instInv p11861) false
  1351473936 17179869184 2 17179869184 84467121 1073741824

noncomputable def p12481 :=
@Enclosure.Real.IsNear.inv_image p11861 218389639103 17179869184 41
  17179869184 675736967 675736969 8589934592
  (p12077 (Eq.refl true)) (Eq.refl true) (Eq.refl true)

noncomputable def p12482 :=
p12152
  (p12479
    (@p12480 1 8589934592
      (p12481 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (Eq.refl true))
    (Eq.refl true))

noncomputable def p12483 :=
@p12062 p11856
  (@p12064 17179869184
    (@p2563 1 0 1
      (BSN.neg_one_pow_even_mk 12 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1))
    p12080 (Eq.refl true))
  (p12482 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p12484 :=
@p11863 p11853 p11855 p11856
  (BSN.hardyZApproximantRS_eq
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
      true 5)
    12
    (p11864 (Eq.refl true) (Eq.refl true)
      (Eq.refl true)))
  (p12057 p12483 (Eq.refl true) (Eq.refl true))

theorem d204 : p11854 p11855 p11856 :=
@p11857 p11853 p11855 p11856
  (@Eq.refl.{1} Real
    (hardyZApproximantRS
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
        true 5)))
  p12484

noncomputable def p12485 :=
Enclosure.Real.IsNear
  (hardyZErrorBoundRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
      true 5))
  false 5972815091 549755813888

noncomputable def p12486 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Real.sqrt p11272)
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p12487 :=
@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 25 4) (@Inv.inv.{0} Real Real.instInv p12486))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 1 32)
    (@Inv.inv.{0} Real Real.instInv
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p12486
          p12486)
        p12486)))

noncomputable def p12488 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZErrorBoundRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
      true 5))
  p12487 false 5972815091

noncomputable def p12489 :=
BSN.hardyZErrorBoundRS_mk
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
    true 5)
  101409000 100000
  (Enclosure.sfrac_ofScientific_eq 101409000 5 100000 (Eq.refl true))
  (Eq.refl true)

noncomputable def p12490 :=
@Enclosure.Real.IsNear.addLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 25 4) (@Inv.inv.{0} Real Real.instInv p12486))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 1 32)
    (@Inv.inv.{0} Real Real.instInv
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p12486
          p12486)
        p12486)))

noncomputable def p12491 :=
@p12490 746601875 68719476736 25 68719476736 91
  549755813888 1 549755813888 410448727694404222976 5972815091
  549755813888

noncomputable def p12492 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 25 4)
  (@Inv.inv.{0} Real Real.instInv p12486) 25 4 0 1
  29864075 17179869184

noncomputable def p12493 :=
@Enclosure.Real.IsNear.recentre' (@Inv.inv.{0} Real Real.instInv p12486) false 29864075
  17179869184 1 17179869184 29864075 17179869184

noncomputable def p12494 :=
@Enclosure.Real.IsNear.mulLit_ff (Real.sqrt p11272)
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p12495 :=
@p12494 3827137167 1073741824 3 8589934592
  277278684194127 1717986918400 101409 1717986918400
  1061183557896198884818209 1844674407370955161600 492085659579129

noncomputable def p12496 :=
@p12495 1844674407370955161600
  (p11472
    (p11481 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (p11476 (p11478 (Eq.refl true))) (Eq.refl true)

noncomputable def p12497 :=
@Enclosure.Real.IsNear.inv_image p12486 1061183557896198884818209
  1844674407370955161600 492085659579129 1844674407370955161600 14932037
  14932038 8589934592 p12496 (Eq.refl true)
  (Eq.refl true)

noncomputable def p12498 :=
@p12491 201 549755813888
  (@p12492 1 17179869184 746601875 68719476736 25
    68719476736 (Enclosure.Real.IsNear.const false 25 4)
    (@p12493 1 17179869184
      (p12497 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (Eq.refl true))
    (Eq.refl true))

noncomputable def p12499 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 1 32)
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p12486
        p12486)
      p12486))
  1

noncomputable def p12500 :=
@p12499 32 0 1 91 17179869184 1
  17179869184 91 549755813888 1 549755813888

noncomputable def p12501 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p12486
        p12486)
      p12486))
  false

noncomputable def p12502 :=
nat_lit 1195009993187999923561125072110171042134288478626042820958751883962303329

noncomputable def p12503 :=
nat_lit 6277101735386680763835789423207666416102355444464034512896000000

noncomputable def p12504 :=
@Enclosure.Real.IsNear.inv_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p12486
      p12486)
    p12486)
  p12502 p12503

noncomputable def p12505 :=
nat_lit 1662428549515202131746267593516605160975981204565436278874915143

noncomputable def p12506 :=
nat_lit 1126110543549235290544813091128227442026977967681

noncomputable def p12507 :=
nat_lit 3402823669209384634633746074317682114560000

noncomputable def p12508 :=
nat_lit 1044386422285904005426828902418643518563

noncomputable def p12509 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p12486
    p12486)
  p12486 p12506 p12507 p12508

noncomputable def p12510 :=
@Enclosure.Real.IsNear.mulLit_ff p12486 p12486 1061183557896198884818209
  1844674407370955161600 492085659579129 1844674407370955161600
  1061183557896198884818209 1844674407370955161600 492085659579129
  1844674407370955161600 p12506

noncomputable def p12511 :=
@p12509 p12507 1061183557896198884818209 1844674407370955161600
  492085659579129 1844674407370955161600 p12502 p12503
  p12505 p12503
  (@p12510 p12507 p12508 p12507
    p12496 p12496 (Eq.refl true))
  p12496

noncomputable def p12512 :=
@p12504 p12505 p12503 45 46
  8589934592 (p12511 (Eq.refl true)) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p12513 :=
p12500 (Enclosure.Real.IsNear.const false 1 32)
  (@p12501 91 17179869184 1 17179869184 91
    17179869184 1 17179869184 (p12512 (Eq.refl true))
    (Eq.refl true))

theorem d205 : p12485 201 549755813888 :=
@p12488 549755813888 201 549755813888
  (p12489 (Eq.refl true))
  (p12498 (p12513 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p12514 :=
Enclosure.Real.IsNear
  (hardyZErrorBoundRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
      true 5))
  false 5963749889 549755813888

noncomputable def p12515 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Real.sqrt p11861)
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p12516 :=
@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 25 4) (@Inv.inv.{0} Real Real.instInv p12515))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 1 32)
    (@Inv.inv.{0} Real Real.instInv
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p12515
          p12515)
        p12515)))

noncomputable def p12517 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZErrorBoundRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
      true 5))
  p12516 false 5963749889

noncomputable def p12518 :=
BSN.hardyZErrorBoundRS_mk
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
    true 5)
  101532300 100000
  (Enclosure.sfrac_ofScientific_eq 101532300 5 100000 (Eq.refl true))
  (Eq.refl true)

noncomputable def p12519 :=
@Enclosure.Real.IsNear.addLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 25 4) (@Inv.inv.{0} Real Real.instInv p12515))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 1 32)
    (@Inv.inv.{0} Real Real.instInv
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p12515
          p12515)
        p12515)))

noncomputable def p12520 :=
@p12519 745468725 68719476736 25 68719476736 89
  549755813888 1 549755813888 409825771756458082304 5963749889
  549755813888

noncomputable def p12521 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 25 4)
  (@Inv.inv.{0} Real Real.instInv p12515) 25 4 0 1
  29818749 17179869184

noncomputable def p12522 :=
@Enclosure.Real.IsNear.recentre' (@Inv.inv.{0} Real Real.instInv p12515) false 29818749
  17179869184 1 17179869184 29818749 17179869184

noncomputable def p12523 :=
nat_lit 42511865096180213267440767

noncomputable def p12524 :=
@Enclosure.Real.IsNear.mulLit_ff (Real.sqrt p11861)
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p12525 :=
@p12524 15313199843 4294967296 3 8589934592
  2776158185881269 17179869184000 1015323 17179869184000
  p12523 73786976294838206464000 19712081284539177

noncomputable def p12526 :=
@p12525 73786976294838206464000
  (p12069
    (p12078 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (p12073 (p12075 (Eq.refl true))) (Eq.refl true)

noncomputable def p12527 :=
@Enclosure.Real.IsNear.inv_image p12515 p12523 73786976294838206464000
  19712081284539177 73786976294838206464000 14909374 14909375
  8589934592 p12526 (Eq.refl true) (Eq.refl true)

noncomputable def p12528 :=
@p12520 201 549755813888
  (@p12521 1 17179869184 745468725 68719476736 25
    68719476736 (Enclosure.Real.IsNear.const false 25 4)
    (@p12522 1 17179869184
      (p12527 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (Eq.refl true))
    (Eq.refl true))

noncomputable def p12529 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 1 32)
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p12515
        p12515)
      p12515))
  1

noncomputable def p12530 :=
@p12529 32 0 1 89 17179869184 1
  17179869184 89 549755813888 1 549755813888

noncomputable def p12531 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p12515
        p12515)
      p12515))
  false

noncomputable def p12532 :=
nat_lit 76829936941111594031350443783336268315659886633012973628733941750101081697663

noncomputable def p12533 :=
@Enclosure.Real.IsNear.inv_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p12515
      p12515)
    p12515)
  p12532 p10376

noncomputable def p12534 :=
nat_lit 106874489699173169860691728195360391947941419414739856466416745966721

noncomputable def p12535 :=
nat_lit 1807258673955825493443934988571298941411305853548289

noncomputable def p12536 :=
nat_lit 1675994681055102672022701267573624724694847

noncomputable def p12537 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p12515
    p12515)
  p12515 p12535 p10380 p12536

noncomputable def p12538 :=
@Enclosure.Real.IsNear.mulLit_ff p12515 p12515 p12523
  73786976294838206464000 19712081284539177 73786976294838206464000
  p12523 73786976294838206464000 19712081284539177
  73786976294838206464000 p12535

noncomputable def p12539 :=
@p12537 p10380 p12523 73786976294838206464000
  19712081284539177 73786976294838206464000 p12532 p10376
  p12534 p10376
  (@p12538 p10380 p12536 p10380
    p12526 p12526 (Eq.refl true))
  p12526

noncomputable def p12540 :=
@p12533 p12534 p10376 44 45
  8589934592 (p12539 (Eq.refl true)) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p12541 :=
p12530 (Enclosure.Real.IsNear.const false 1 32)
  (@p12531 89 17179869184 1 17179869184 89
    17179869184 1 17179869184 (p12540 (Eq.refl true))
    (Eq.refl true))

theorem d206 : p12514 201 549755813888 :=
@p12517 549755813888 201 549755813888
  (p12518 (Eq.refl true))
  (p12528 (p12541 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p12542 :=
@LE.le.{0} Real Real.instLE
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@OfNat.ofNat.{0} Real 32
      (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
    Real.pi)
  (@Prod.fst.{0, 0} Real Real (@NonemptyInterval.toProd.{0} Real Real.instLE d29))

noncomputable def p12543 :=
@OfNat.ofNat.{0} Real 101409
  (@instOfNatAtLeastTwo.{0} Real 101409
    (@AddMonoidWithOne.toNatCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real
            (@DivisionSemiring.toSemiring.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))))))
    (Mathlib.Meta.NormNum.instAtLeastTwo 101407))

noncomputable def p12544 :=
@OfNat.ofNat.{0} Real 100
  (@instOfNatAtLeastTwo.{0} Real 100
    (@AddMonoidWithOne.toNatCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real
            (@DivisionSemiring.toSemiring.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))))))
    (Mathlib.Meta.NormNum.instAtLeastTwo 98))

noncomputable def p12545 :=
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
    p12543 p12544)

noncomputable def p12546 :=
@congrArg.{1, 1} Real Prop (@Prod.fst.{0, 0} Real Real (@NonemptyInterval.toProd.{0} Real Real.instLE d29))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real
    (@instHDiv.{0} Real
      (@DivInvMonoid.toDiv.{0} Real
        (@GroupWithZero.toDivInvMonoid.{0} Real
          (@DivisionSemiring.toGroupWithZero.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p12543 p12544)

noncomputable def p12547 :=
p12546
  (@LE.le.{0} Real Real.instLE
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 32
        (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
      Real.pi))

noncomputable def p12548 :=
@Mathlib.Meta.NormNum.IsNNRat.to_eq.{0} Real
  (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)) 101409 100
  (@Prod.fst.{0, 0} Real Real (@NonemptyInterval.toProd.{0} Real Real.instLE d29)) p12543
  p12544
  (@Mathlib.Meta.NormNum.isNNRat_ofScientific_of_true.{0} Real
    (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)) 101409000
    5 101409 100
    (p178
      (p179 p4
        (@p180 101409 100
          (p184 (@Eq.refl.{1} Nat (Nat.mul 101409000 1))
            (@Eq.refl.{1} Nat 100000))))))
  (@Eq.refl.{1} Real p12543)

noncomputable def p12549 :=
@congrArg.{1, 1} Real Prop
  (@HDiv.hDiv.{0, 0, 0} Real Real Real
    (@instHDiv.{0} Real
      (@DivInvMonoid.toDiv.{0} Real
        (@GroupWithZero.toDivInvMonoid.{0} Real
          (@DivisionSemiring.toGroupWithZero.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p12543 p12544)

noncomputable def p12550 :=
@p12549
  (@HDiv.hDiv.{0, 0, 0} Real Real Real
    (@instHDiv.{0} Real
      (@DivInvMonoid.toDiv.{0} Real
        (@GroupWithZero.toDivInvMonoid.{0} Real
          (@DivisionSemiring.toGroupWithZero.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p12543 p12544)

noncomputable def p12551 :=
p12550
  (@LE.le.{0} Real Real.instLE
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 32
        (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
      Real.pi))

noncomputable def p12552 :=
@Mathlib.Meta.NormNum.IsNNRat.to_eq.{0} Real
  (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)) 101409 100
  (@HDiv.hDiv.{0, 0, 0} Real Real Real
    (@instHDiv.{0} Real
      (@DivInvMonoid.toDiv.{0} Real
        (@GroupWithZero.toDivInvMonoid.{0} Real
          (@DivisionSemiring.toGroupWithZero.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p12543 p12544)

noncomputable def p12553 :=
@Mathlib.Meta.NormNum.isNNRat_mul.{0} Real
  (@DivisionSemiring.toSemiring.{0} Real
    (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real (@Distrib.toMul.{0} Real (@instDistribOfSemiring.{0} Real Real.semiring))))
  p12543
  (@Inv.inv.{0} Real
    (@InvOneClass.toInv.{0} Real
      (@DivInvOneMonoid.toInvOneClass.{0} Real
        (@DivisionMonoid.toDivInvOneMonoid.{0} Real
          (@GroupWithZero.toDivisionMonoid.{0} Real
            (@DivisionSemiring.toGroupWithZero.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))))))
    p12544)

noncomputable def p12554 :=
@p12553 101409 1 101409 1 100 100
  1
  (@Eq.refl.{1} (Real → Real → Real)
    (@HMul.hMul.{0, 0, 0} Real Real Real
      (@instHMul.{0} Real (@Distrib.toMul.{0} Real (@instDistribOfSemiring.{0} Real Real.semiring)))))
  (@Mathlib.Meta.NormNum.IsNat.to_isNNRat.{0} Real
    (@DivisionSemiring.toSemiring.{0} Real
      (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))
    p12543 101409
    (@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
      (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
      p12543 101409
      (@Eq.refl.{1} Real
        (@OfNat.ofNat.{0} Real 101409
          (@instOfNatAtLeastTwo.{0} Real 101409
            (@AddMonoidWithOne.toNatCast.{0} Real
              (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 101407))))))

noncomputable def p12555 :=
@Mathlib.Meta.NormNum.isNNRat_inv_pos.{0} Real
  (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))
  (@FloorSemiring.instCharZero.{0} Real Real.semiring Real.partialOrder
    (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing))
  p12544 99 1
  (@Mathlib.Meta.NormNum.IsNat.to_isNNRat.{0} Real
    (@DivisionSemiring.toSemiring.{0} Real
      (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))
    p12544 100
    (@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
      (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
      p12544 100
      (@Eq.refl.{1} Real
        (@OfNat.ofNat.{0} Real 100
          (@instOfNatAtLeastTwo.{0} Real 100
            (@AddMonoidWithOne.toNatCast.{0} Real
              (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 98))))))

noncomputable def p12556 :=
@p12552 p12543 p12544
  (@Mathlib.Meta.NormNum.isNNRat_div.{0} Real
    (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)) p12543
    p12544 101409 100
    (p12554 p12555 (@Eq.refl.{1} Nat (Nat.mul 101409 1))
      (@Eq.refl.{1} Nat 100)))
  (@Eq.refl.{1} Real p12543)

noncomputable def p12557 :=
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
    p12543 p12544)

noncomputable def p12558 :=
@LT.lt.{0} Real
  (@Preorder.toLT.{0} Real (@PartialOrder.toPreorder.{0} Real (@LinearOrder.toPartialOrder.{0} Real Real.linearOrder)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real
    (@instHDiv.{0} Real
      (@DivInvMonoid.toDiv.{0} Real
        (@GroupWithZero.toDivInvMonoid.{0} Real
          (@DivisionSemiring.toGroupWithZero.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p12543 p12544)

noncomputable def p12559 :=
@HMul.hMul.{0, 0, 0} Real Real Real
  (@instHMul.{0} Real (@Distrib.toMul.{0} Real (@instDistribOfSemiring.{0} Real Real.semiring)))
  (@OfNat.ofNat.{0} Real 91329
    (@instOfNatAtLeastTwo.{0} Real 91329
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))))
      (@Nat.instAtLeastTwoHAddOfNat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) 91327
          (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
        (@instNeZeroNatHAdd_1 91327 (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))

noncomputable def p12560 :=
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
  p12543

noncomputable def p12561 :=
@HMul.hMul.{0, 0, 0} Real Real Real
  (@instHMul.{0} Real
    (@Distrib.toMul.{0} Real
      (@instDistribOfSemiring.{0} Real
        (@DivisionSemiring.toSemiring.{0} Real
          (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
  (@OfNat.ofNat.{0} Real 100
    (@instOfNatAtLeastTwo.{0} Real 100
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 98)))

noncomputable def p12562 :=
@HSub.hSub.{0, 0, 0} Real Real Real
  (@instHSub.{0} Real
    (@SubNegMonoid.toSub.{0} Real
      (@AddGroup.toSubNegMonoid.{0} Real
        (@AddGroupWithOne.toAddGroup.{0} Real
          (@Ring.toAddGroupWithOne.{0} Real
            (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField)))))))
  p12560
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real
          (@DivisionSemiring.toSemiring.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p3705 (p12561 Real.pi))

noncomputable def p12563 :=
@HAdd.hAdd.{0, 0, 0} Real Real Real
  (@instHAdd.{0} Real (@AddSemigroup.toAdd.{0} Real (@AddMonoid.toAddSemigroup.{0} Real Real.instAddMonoid)))
  (p12559
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
  p12562

noncomputable def p12564 :=
@HMul.hMul.{0, 0, 0} Real Real Real
  (@instHMul.{0} Real (@Distrib.toMul.{0} Real (@instDistribOfSemiring.{0} Real Real.semiring)))
  (@OfNat.ofNat.{0} Real 160
    (@instOfNatAtLeastTwo.{0} Real 160
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))))
      (@Nat.instAtLeastTwoHAddOfNat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) 158
          (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
        (@instNeZeroNatHAdd_1 158 (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))

noncomputable def p12565 :=
@Eq.mp.{0}
  (@LT.lt.{0} Real (@Preorder.toLT.{0} Real (@PartialOrder.toPreorder.{0} Real Real.partialOrder))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real (@AddSemigroup.toAdd.{0} Real (@AddMonoid.toAddSemigroup.{0} Real Real.instAddMonoid)))
      p12563 (p12564 p3713))
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real (@MulZeroClass.toZero.{0} Real (@instMulZeroClassOfSemiring.{0} Real Real.semiring)))))
  (@LT.lt.{0} Real (@Preorder.toLT.{0} Real (@PartialOrder.toPreorder.{0} Real Real.partialOrder))
    (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real (@MulZeroClass.toZero.{0} Real (@instMulZeroClassOfSemiring.{0} Real Real.semiring)))))

noncomputable def p12566 :=
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
    (Int.negOfNat 3200))

noncomputable def p12567 :=
@Mathlib.Tactic.Ring.Common.add_congr.{0} Real Real.instCommSemiring p12563
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@Mathlib.Meta.NormNum.instAddMonoidWithOne.{0} Real
        (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)))
      10080)
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p12566
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))
  (p12564 p3713)

noncomputable def p12568 :=
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
    3200)

noncomputable def p12569 :=
@p12567
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 10080))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p12568
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))

noncomputable def p12570 :=
@Mathlib.Tactic.Ring.Common.add_congr.{0} Real Real.instCommSemiring
  (p12559
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
      (Int.negOfNat 91329))
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))

noncomputable def p12571 :=
@p12570 p12562
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      101409)
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p12566
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
      10080)
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p12566
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))

noncomputable def p12572 :=
@Mathlib.Tactic.Ring.Common.mul_congr.{0} Real Real.instCommSemiring
  (@OfNat.ofNat.{0} Real 91329
    (@instOfNatAtLeastTwo.{0} Real 91329
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))))
      (@Nat.instAtLeastTwoHAddOfNat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) 91327
          (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
        (@instNeZeroNatHAdd_1 91327 (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))

noncomputable def p12573 :=
@p12572
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      91329)
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

noncomputable def p12574 :=
@Mathlib.Tactic.Ring.cast_pos.{0} Real Real.instCommSemiring
  (@OfNat.ofNat.{0} Real 91329
    (@instOfNatAtLeastTwo.{0} Real 91329
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))))
      (@Nat.instAtLeastTwoHAddOfNat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) 91327
          (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
        (@instNeZeroNatHAdd_1 91327 (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))

noncomputable def p12575 :=
@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
  (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
  (@OfNat.ofNat.{0} Real 91329
    (@instOfNatAtLeastTwo.{0} Real 91329
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))))
      (@Nat.instAtLeastTwoHAddOfNat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) 91327
          (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
        (@instNeZeroNatHAdd_1 91327 (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))

noncomputable def p12576 :=
@p12573
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
      (Int.negOfNat 91329))
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@p12574 91329
    (@p12575 91329
      (@Eq.refl.{1} Real
        (@OfNat.ofNat.{0} Real 91329
          (@instOfNatAtLeastTwo.{0} Real 91329
            (@AddMonoidWithOne.toNatCast.{0} Real
              (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 91327))))))

noncomputable def p12577 :=
@Mathlib.Tactic.Ring.Common.add_mul.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    91329)
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
      (Int.negOfNat 91329))
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))

noncomputable def p12578 :=
@Mathlib.Tactic.Ring.Common.mul_add.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    91329)
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 1))
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 91329))

noncomputable def p12579 :=
@Mathlib.Meta.NormNum.IsInt.to_raw_eq.{0} Real
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      91329)
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 1)))
  (Int.negOfNat 91329)

noncomputable def p12580 :=
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
    91329)
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 1))

noncomputable def p12581 :=
@p12580 (Int.ofNat 91329) (Int.negOfNat 1) (Int.negOfNat 91329)
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
      91329)
    91329
    (@Mathlib.Meta.NormNum.IsNat.of_raw.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      91329))

noncomputable def p12582 :=
@p12578
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 91329))
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@p12579 (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (p12581
      (@Mathlib.Meta.NormNum.IsInt.of_raw.{0} Real
        (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)) (Int.negOfNat 1))
      (@Eq.refl.{1} Int (Int.negOfNat 91329))))
  (@Mathlib.Tactic.Ring.Common.mul_zero.{0} Real Real.instCommSemiring
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      91329))

noncomputable def p12583 :=
@p12577
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 91329))
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (p12582
    (@Mathlib.Tactic.Ring.Common.add_pf_add_zero.{0} Real Real.instCommSemiring
      (@HAdd.hAdd.{0, 0, 0} Real Real Real
        (@instHAdd.{0} Real
          (@Distrib.toAdd.{0} Real
            (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
        (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
          (Int.negOfNat 91329))
        (@OfNat.ofNat.{0} Real 0
          (@Zero.toOfNat0.{0} Real
            (@MulZeroClass.toZero.{0} Real
              (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))))

noncomputable def p12584 :=
p12583
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
        (Int.negOfNat 91329))
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))

noncomputable def p12585 :=
p12571
  (p12576
    (p3726 p3727
      (p3728
        (@Mathlib.Meta.NormNum.IsInt.to_raw_eq.{0} Real p3729 (Int.negOfNat 1)
          (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
          (p3733 (@Eq.refl.{1} Int (Int.negOfNat 1))))
        (@Mathlib.Tactic.Ring.Common.neg_zero.{0} Real Real.commRing)))
    p12584)

noncomputable def p12586 :=
@Mathlib.Tactic.Ring.Common.sub_congr.{0} Real Real.commRing p12560
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      101409)
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
    p3705 (p12561 Real.pi))

noncomputable def p12587 :=
@p3744 p12543
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      101409)
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
      101409)
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))

noncomputable def p12588 :=
p12587
  (p3746
    (p3747
      (@Nat.cast_one.{0} Real
        (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))))
  (@Mathlib.Tactic.Ring.cast_pos.{0} Real Real.instCommSemiring p12543 101409
    (@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
      (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
      p12543 101409
      (@Eq.refl.{1} Real
        (@OfNat.ofNat.{0} Real 101409
          (@instOfNatAtLeastTwo.{0} Real 101409
            (@AddMonoidWithOne.toNatCast.{0} Real
              (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 101407))))))

noncomputable def p12589 :=
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
      101409)
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
      101409)
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))

noncomputable def p12590 :=
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
    101409)
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    101409)

noncomputable def p12591 :=
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
      101409))
  101409

noncomputable def p12592 :=
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
    101409)
  1 101409

noncomputable def p12593 :=
@p12592 101409
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
    101409)
  (@Eq.refl.{1} Nat 101409)

noncomputable def p12594 :=
@p12590
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
      101409)
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@p12591
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p12593)

noncomputable def p12595 :=
p12594
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
        101409)
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))

noncomputable def p12596 :=
@p12589
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
      101409)
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  p12595

noncomputable def p12597 :=
p12596
  (@Mathlib.Tactic.Ring.Common.zero_mul.{0} Real Real.instCommSemiring
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      (@Nat.rawCast.{0} Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
            (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
        101409)
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))

noncomputable def p12598 :=
p12597
  (@Mathlib.Tactic.Ring.Common.add_pf_add_zero.{0} Real Real.instCommSemiring
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      (@Nat.rawCast.{0} Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
            (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
        101409)
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))

noncomputable def p12599 :=
@p12586
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p12568
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
      101409)
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p12566
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))
  (p12588 p12598)

noncomputable def p12600 :=
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
  (p12561 Real.pi)

noncomputable def p12601 :=
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
    100)

noncomputable def p12602 :=
@p12600
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p12601
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p12568
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

noncomputable def p12603 :=
@Mathlib.Tactic.Ring.Common.mul_congr.{0} Real Real.instCommSemiring
  (@OfNat.ofNat.{0} Real 100
    (@instOfNatAtLeastTwo.{0} Real 100
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 98)))

noncomputable def p12604 :=
@p12603
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      100)
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  Real.pi

noncomputable def p12605 :=
@Mathlib.Tactic.Ring.cast_pos.{0} Real Real.instCommSemiring
  (@OfNat.ofNat.{0} Real 100
    (@instOfNatAtLeastTwo.{0} Real 100
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 98)))

noncomputable def p12606 :=
@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
  (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
  (@OfNat.ofNat.{0} Real 100
    (@instOfNatAtLeastTwo.{0} Real 100
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 98)))

noncomputable def p12607 :=
@p12604
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
    p12601
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@p12605 100
    (@p12606 100
      (@Eq.refl.{1} Real
        (@OfNat.ofNat.{0} Real 100
          (@instOfNatAtLeastTwo.{0} Real 100
            (@AddMonoidWithOne.toNatCast.{0} Real
              (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 98))))))

noncomputable def p12608 :=
p12607
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

noncomputable def p12609 :=
@Mathlib.Tactic.Ring.Common.add_mul.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    100)
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
    p12601
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))

noncomputable def p12610 :=
@Mathlib.Tactic.Ring.Common.mul_add.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    100)
  p3777
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  p12601

noncomputable def p12611 :=
@Mathlib.Tactic.Ring.Common.mul_pf_right.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    100)
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1)
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    100)
  Real.pi

noncomputable def p12612 :=
@Mathlib.Meta.NormNum.IsNat.to_raw_eq.{0} Real
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      100)
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      1))
  100

noncomputable def p12613 :=
@Mathlib.Meta.NormNum.isNat_mul.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    100)
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1)
  100 1

noncomputable def p12614 :=
@p12613 100
  (@Eq.refl.{1} (Real → Real → Real)
    (@HMul.hMul.{0, 0, 0} Real Real Real
      (@instHMul.{0} Real
        (@Distrib.toMul.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@Mathlib.Meta.NormNum.IsNat.of_raw.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    100)
  (@Mathlib.Meta.NormNum.IsNat.of_raw.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1)
  (@Eq.refl.{1} Nat 100)

noncomputable def p12615 :=
@p12610
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p12601
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (p12611
    (@Nat.rawCast.{0} Nat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat
          (@Semiring.toNonAssocSemiring.{0} Nat (@CommSemiring.toSemiring.{0} Nat Nat.instCommSemiring))))
      1)
    (@p12612
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p12614))
  (@Mathlib.Tactic.Ring.Common.mul_zero.{0} Real Real.instCommSemiring
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      100))

noncomputable def p12616 :=
@p12609
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p12601
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (p12615
    (@Mathlib.Tactic.Ring.Common.add_pf_add_zero.{0} Real Real.instCommSemiring
      (@HAdd.hAdd.{0, 0, 0} Real Real Real
        (@instHAdd.{0} Real
          (@Distrib.toAdd.{0} Real
            (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
        p12601
        (@OfNat.ofNat.{0} Real 0
          (@Zero.toOfNat0.{0} Real
            (@MulZeroClass.toZero.{0} Real
              (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))))

noncomputable def p12617 :=
p12616
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
      p12601
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))

noncomputable def p12618 :=
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
    p12601
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p12568
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))

noncomputable def p12619 :=
@Mathlib.Tactic.Ring.Common.mul_add.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    32)
  p12601
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  p12568

noncomputable def p12620 :=
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
    100)
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    3200)
  Real.pi

noncomputable def p12621 :=
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
      100))
  3200

noncomputable def p12622 :=
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
    100)
  32 100

noncomputable def p12623 :=
@p12622 3200
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
    100)
  (@Eq.refl.{1} Nat 3200)

noncomputable def p12624 :=
@p12619
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p12568
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (p12620
    (@Nat.rawCast.{0} Nat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat
          (@Semiring.toNonAssocSemiring.{0} Nat (@CommSemiring.toSemiring.{0} Nat Nat.instCommSemiring))))
      1)
    (@p12621
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p12623))
  (@Mathlib.Tactic.Ring.Common.mul_zero.{0} Real Real.instCommSemiring
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      32))

noncomputable def p12625 :=
@p12618
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p12568
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (p12624
    (@Mathlib.Tactic.Ring.Common.add_pf_add_zero.{0} Real Real.instCommSemiring
      (@HAdd.hAdd.{0, 0, 0} Real Real Real
        (@instHAdd.{0} Real
          (@Distrib.toAdd.{0} Real
            (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
        p12568
        (@OfNat.ofNat.{0} Real 0
          (@Zero.toOfNat0.{0} Real
            (@MulZeroClass.toZero.{0} Real
              (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))))

noncomputable def p12626 :=
p12625
  (@Mathlib.Tactic.Ring.Common.zero_mul.{0} Real Real.instCommSemiring
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p12601
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))
  (@Mathlib.Tactic.Ring.Common.add_pf_add_zero.{0} Real Real.instCommSemiring
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p12568
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))

noncomputable def p12627 :=
@Mathlib.Tactic.Ring.Common.sub_pf.{0} Real Real.commRing
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      101409)
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p12568
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))

noncomputable def p12628 :=
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
    3200)

noncomputable def p12629 :=
@p3730
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    3200)
  (Int.ofNat 3200) (Int.negOfNat 3200) p3731

noncomputable def p12630 :=
p12629
  (@Mathlib.Meta.NormNum.IsNat.to_isInt.{0} Real
    (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      3200)
    3200
    (@Mathlib.Meta.NormNum.IsNat.of_raw.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      3200))

noncomputable def p12631 :=
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
    3200)
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 3200))
  (@Mathlib.Meta.NormNum.IsInt.to_raw_eq.{0} Real p12628 (Int.negOfNat 3200)
    (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (p12630 (@Eq.refl.{1} Int (Int.negOfNat 3200))))

noncomputable def p12632 :=
@Mathlib.Tactic.Ring.Common.neg_add.{0} Real Real.commRing p12568
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  p12566
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  p12631 (@Mathlib.Tactic.Ring.Common.neg_zero.{0} Real Real.commRing)

noncomputable def p12633 :=
@p12627
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p12566
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
      101409)
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p12566
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))
  p12632

noncomputable def p12634 :=
@Mathlib.Tactic.Ring.Common.add_pf_add_lt.{0} Real Real.instCommSemiring
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p12566
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p12566
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    101409)

noncomputable def p12635 :=
p12633
  (p12634
    (@Mathlib.Tactic.Ring.Common.add_pf_zero_add.{0} Real Real.instCommSemiring
      (@HAdd.hAdd.{0, 0, 0} Real Real Real
        (@instHAdd.{0} Real
          (@Distrib.toAdd.{0} Real
            (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
        p12566
        (@OfNat.ofNat.{0} Real 0
          (@Zero.toOfNat0.{0} Real
            (@MulZeroClass.toZero.{0} Real
              (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))))

noncomputable def p12636 :=
@Mathlib.Tactic.Ring.Common.add_pf_add_overlap.{0} Real Real.instCommSemiring
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 91329))
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    101409)
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p12566
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@Nat.rawCast.{0} Real
    (@Mathlib.Meta.NormNum.instAddMonoidWithOne.{0} Real
      (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)))
    10080)
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p12566
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))

noncomputable def p12637 :=
@Mathlib.Meta.NormNum.IsNat.to_raw_eq.{0} Real
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 91329))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      101409))
  10080
  (@Mathlib.Meta.NormNum.instAddMonoidWithOne.{0} Real
    (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)))

noncomputable def p12638 :=
@Mathlib.Meta.NormNum.isInt_add.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 91329))
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    101409)
  (Int.negOfNat 91329) (Int.ofNat 101409)

noncomputable def p12639 :=
@p12638 (Int.ofNat 10080)
  (@Eq.refl.{1} (Real → Real → Real)
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@Mathlib.Meta.NormNum.IsInt.of_raw.{0} Real
    (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)) (Int.negOfNat 91329))
  (@Mathlib.Meta.NormNum.IsNat.to_isInt.{0} Real
    (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      101409)
    101409
    (@Mathlib.Meta.NormNum.IsNat.of_raw.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      101409))

noncomputable def p12640 :=
@Mathlib.Meta.NormNum.IsInt.to_isNat.{0} Real
  (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 91329))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      101409))
  10080 (p12639 (@Eq.refl.{1} Int (Int.ofNat 10080)))

noncomputable def p12641 :=
p12585
  (p12599
    (p12602 (p12608 p12617) p12626)
    p12635)
  (p12636 (p12637 p12640)
    (@Mathlib.Tactic.Ring.Common.add_pf_zero_add.{0} Real Real.instCommSemiring
      (@HAdd.hAdd.{0, 0, 0} Real Real Real
        (@instHAdd.{0} Real
          (@Distrib.toAdd.{0} Real
            (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
        p12566
        (@OfNat.ofNat.{0} Real 0
          (@Zero.toOfNat0.{0} Real
            (@MulZeroClass.toZero.{0} Real
              (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))))

noncomputable def p12642 :=
@Mathlib.Tactic.Ring.Common.mul_congr.{0} Real Real.instCommSemiring
  (@OfNat.ofNat.{0} Real 160
    (@instOfNatAtLeastTwo.{0} Real 160
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))))
      (@Nat.instAtLeastTwoHAddOfNat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) 158
          (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
        (@instNeZeroNatHAdd_1 158 (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))

noncomputable def p12643 :=
@p12642
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      160)
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  p3713

noncomputable def p12644 :=
@p12643
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
      (Int.negOfNat 10080))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p12568
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))

noncomputable def p12645 :=
@Mathlib.Tactic.Ring.cast_pos.{0} Real Real.instCommSemiring
  (@OfNat.ofNat.{0} Real 160
    (@instOfNatAtLeastTwo.{0} Real 160
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))))
      (@Nat.instAtLeastTwoHAddOfNat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) 158
          (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
        (@instNeZeroNatHAdd_1 158 (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))

noncomputable def p12646 :=
@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
  (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
  (@OfNat.ofNat.{0} Real 160
    (@instOfNatAtLeastTwo.{0} Real 160
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))))
      (@Nat.instAtLeastTwoHAddOfNat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) 158
          (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
        (@instNeZeroNatHAdd_1 158 (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))

noncomputable def p12647 :=
p12644
  (@p12645 160
    (@p12646 160
      (@Eq.refl.{1} Real
        (@OfNat.ofNat.{0} Real 160
          (@instOfNatAtLeastTwo.{0} Real 160
            (@AddMonoidWithOne.toNatCast.{0} Real
              (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 158))))))

noncomputable def p12648 :=
@Mathlib.Tactic.Ring.Common.add_mul.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    160)
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
      (Int.negOfNat 10080))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p12568
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))

noncomputable def p12649 :=
@Mathlib.Tactic.Ring.Common.mul_add.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    160)
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
    (Int.negOfNat 10080))

noncomputable def p12650 :=
@Mathlib.Meta.NormNum.IsInt.to_raw_eq.{0} Real
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      160)
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 63)))
  (Int.negOfNat 10080)

noncomputable def p12651 :=
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
    160)
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 63))

noncomputable def p12652 :=
@p12651 (Int.ofNat 160) (Int.negOfNat 63) (Int.negOfNat 10080)
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
      160)
    160
    (@Mathlib.Meta.NormNum.IsNat.of_raw.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      160))

noncomputable def p12653 :=
@p12649
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p12568
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 10080))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p12568
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))
  (@p12650 (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (p12652
      (@Mathlib.Meta.NormNum.IsInt.of_raw.{0} Real
        (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)) (Int.negOfNat 63))
      (@Eq.refl.{1} Int (Int.negOfNat 10080))))

noncomputable def p12654 :=
@Mathlib.Tactic.Ring.Common.mul_add.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    160)
  p3819
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  p12568

noncomputable def p12655 :=
@Mathlib.Tactic.Ring.Common.mul_pf_right.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    160)
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    20)
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    3200)
  Real.pi

noncomputable def p12656 :=
@Mathlib.Meta.NormNum.IsNat.to_raw_eq.{0} Real
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      160)
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      20))
  3200

noncomputable def p12657 :=
@Mathlib.Meta.NormNum.isNat_mul.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    160)
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    20)
  160 20

noncomputable def p12658 :=
@p12657 3200
  (@Eq.refl.{1} (Real → Real → Real)
    (@HMul.hMul.{0, 0, 0} Real Real Real
      (@instHMul.{0} Real
        (@Distrib.toMul.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@Mathlib.Meta.NormNum.IsNat.of_raw.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    160)
  (@Mathlib.Meta.NormNum.IsNat.of_raw.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    20)
  (@Eq.refl.{1} Nat 3200)

noncomputable def p12659 :=
@p12654
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p12568
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (p12655
    (@Nat.rawCast.{0} Nat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat
          (@Semiring.toNonAssocSemiring.{0} Nat (@CommSemiring.toSemiring.{0} Nat Nat.instCommSemiring))))
      1)
    (@p12656
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p12658))
  (@Mathlib.Tactic.Ring.Common.mul_zero.{0} Real Real.instCommSemiring
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      160))

noncomputable def p12660 :=
p12653
  (p12659
    (@Mathlib.Tactic.Ring.Common.add_pf_add_zero.{0} Real Real.instCommSemiring
      (@HAdd.hAdd.{0, 0, 0} Real Real Real
        (@instHAdd.{0} Real
          (@Distrib.toAdd.{0} Real
            (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
        p12568
        (@OfNat.ofNat.{0} Real 0
          (@Zero.toOfNat0.{0} Real
            (@MulZeroClass.toZero.{0} Real
              (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))))

noncomputable def p12661 :=
@Mathlib.Tactic.Ring.Common.add_pf_add_lt.{0} Real Real.instCommSemiring
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p12568
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p12568
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 10080))

noncomputable def p12662 :=
p12660
  (p12661
    (@Mathlib.Tactic.Ring.Common.add_pf_zero_add.{0} Real Real.instCommSemiring
      (@HAdd.hAdd.{0, 0, 0} Real Real Real
        (@instHAdd.{0} Real
          (@Distrib.toAdd.{0} Real
            (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
        p12568
        (@OfNat.ofNat.{0} Real 0
          (@Zero.toOfNat0.{0} Real
            (@MulZeroClass.toZero.{0} Real
              (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))))

noncomputable def p12663 :=
@p12648
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 10080))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p12568
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))
  p12662

noncomputable def p12664 :=
p12663
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

noncomputable def p12665 :=
p12664
  (@Mathlib.Tactic.Ring.Common.add_pf_add_zero.{0} Real Real.instCommSemiring
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
        (Int.negOfNat 10080))
      (@HAdd.hAdd.{0, 0, 0} Real Real Real
        (@instHAdd.{0} Real
          (@Distrib.toAdd.{0} Real
            (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
        p12568
        (@OfNat.ofNat.{0} Real 0
          (@Zero.toOfNat0.{0} Real
            (@MulZeroClass.toZero.{0} Real
              (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))))

noncomputable def p12666 :=
@Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@Mathlib.Meta.NormNum.instAddMonoidWithOne.{0} Real
      (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)))
    10080)
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p12566
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 10080))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p12568
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))

noncomputable def p12667 :=
@Mathlib.Meta.NormNum.isInt_add.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@Nat.rawCast.{0} Real
    (@Mathlib.Meta.NormNum.instAddMonoidWithOne.{0} Real
      (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)))
    10080)
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 10080))
  (Int.ofNat 10080) (Int.negOfNat 10080)

noncomputable def p12668 :=
@p12667 (Int.ofNat 0)
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
      10080)
    10080
    (@Mathlib.Meta.NormNum.IsNat.of_raw.{0} Real
      (@Mathlib.Meta.NormNum.instAddMonoidWithOne.{0} Real
        (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)))
      10080))
  (@Mathlib.Meta.NormNum.IsInt.of_raw.{0} Real
    (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)) (Int.negOfNat 10080))

noncomputable def p12669 :=
@Mathlib.Meta.NormNum.IsInt.to_isNat.{0} Real
  (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@Mathlib.Meta.NormNum.instAddMonoidWithOne.{0} Real
        (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)))
      10080)
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 10080)))
  0 (p12668 (@Eq.refl.{1} Int (Int.ofNat 0)))

noncomputable def p12670 :=
@Mathlib.Meta.NormNum.isInt_add.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 3200))
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    3200)
  (Int.negOfNat 3200) (Int.ofNat 3200)

noncomputable def p12671 :=
@p12670 (Int.ofNat 0)
  (@Eq.refl.{1} (Real → Real → Real)
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@Mathlib.Meta.NormNum.IsInt.of_raw.{0} Real
    (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)) (Int.negOfNat 3200))
  (@Mathlib.Meta.NormNum.IsNat.to_isInt.{0} Real
    (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      3200)
    3200
    (@Mathlib.Meta.NormNum.IsNat.of_raw.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      3200))

noncomputable def p12672 :=
@Mathlib.Meta.NormNum.IsInt.to_isNat.{0} Real
  (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 3200))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      3200))
  0 (p12671 (@Eq.refl.{1} Int (Int.ofNat 0)))

noncomputable def p12673 :=
@Mathlib.Tactic.Ring.Common.add_overlap_pf_zero.{0} Real Real.instCommSemiring
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 3200))
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    3200)
  Real.pi
  (@Nat.rawCast.{0} Nat
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat
        (@Semiring.toNonAssocSemiring.{0} Nat (@CommSemiring.toSemiring.{0} Nat Nat.instCommSemiring))))
    1)
  p12672

noncomputable def p12674 :=
@Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero.{0} Real Real.instCommSemiring p12566
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  p12568
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  p12673

noncomputable def p12675 :=
@Mathlib.Tactic.Ring.of_eq.{1} Real
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real (@AddSemigroup.toAdd.{0} Real (@AddMonoid.toAddSemigroup.{0} Real Real.instAddMonoid)))
    p12563 (p12564 p3713))
  (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (p12569 p12641
    (p12647
      (p3840 (p3842 p3852) p3860)
      p12665)
    (@p12666
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
      p12669
      (p12674
        (@Mathlib.Tactic.Ring.Common.add_pf_zero_add.{0} Real Real.instCommSemiring
          (@OfNat.ofNat.{0} Real 0
            (@Zero.toOfNat0.{0} Real
              (@MulZeroClass.toZero.{0} Real
                (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))))

noncomputable def p12676 :=
@congrArg.{1, 1} Real Prop
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real (@AddSemigroup.toAdd.{0} Real (@AddMonoid.toAddSemigroup.{0} Real Real.instAddMonoid)))
    p12563 (p12564 p3713))
  (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
  (fun (_a : Real) =>
    @LT.lt.{0} Real (@Preorder.toLT.{0} Real (@PartialOrder.toPreorder.{0} Real Real.partialOrder)) _a
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real (@MulZeroClass.toZero.{0} Real (@instMulZeroClassOfSemiring.{0} Real Real.semiring)))))
  (p12675
    (@Mathlib.Tactic.Ring.cast_zero.{0} Real Real.instCommSemiring
      (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
      (@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
        (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
        (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) 0
        (@Nat.cast_zero.{0} Real
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))))))

noncomputable def p12677 :=
@HAdd.hAdd.{0, 0, 0} Real Real Real
  (@instHAdd.{0} Real (@Distrib.toAdd.{0} Real (@instDistribOfSemiring.{0} Real Real.semiring)))
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real (@instDistribOfSemiring.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))))
    (@OfNat.ofNat.{0} Real 91329
      (@instOfNatAtLeastTwo.{0} Real 91329 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 91328 (instOfNatNat 91328))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 91327 (instOfNatNat 91327))))))
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
  p12562

noncomputable def p12678 :=
@Mathlib.Tactic.Linarith.add_neg.{0} Real Real.semiring Real.partialOrder Real.instIsStrictOrderedRing
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real (@instDistribOfSemiring.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))))
    (@OfNat.ofNat.{0} Real 91329
      (@instOfNatAtLeastTwo.{0} Real 91329 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 91328 (instOfNatNat 91328))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 91327 (instOfNatNat 91327))))))
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
  p12562

noncomputable def p12679 :=
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
  (@OfNat.ofNat.{0} Real 91329
    (@instOfNatAtLeastTwo.{0} Real 91329 Real.instNatCast
      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 91328 (instOfNatNat 91328))
        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 91327 (instOfNatNat 91327))))))
  (@neg_neg_of_pos.{0} Real Real.instAddCommGroup Real.partialOrder Real.instIsOrderedAddMonoid
    (@OfNat.ofNat.{0} Real 1
      (@One.toOfNat1.{0} Real
        (@AddMonoidWithOne.toOne.{0} Real
          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
            (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
              (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))))))
    (@Mathlib.Tactic.Linarith.zero_lt_one.{0} Real Real.semiring Real.partialOrder Real.instIsStrictOrderedRing))

noncomputable def p12680 :=
@Mathlib.Meta.NormNum.isNat_lt_true.{0} Real Real.semiring Real.partialOrder Real.instIsOrderedRing
  (@FloorSemiring.instCharZero.{0} Real (@Ring.toSemiring.{0} Real Real.instRing) Real.partialOrder
    (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing))
  (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
  (@OfNat.ofNat.{0} Real 91329
    (@instOfNatAtLeastTwo.{0} Real 91329 Real.instNatCast
      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 91328 (instOfNatNat 91328))
        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 91327 (instOfNatNat 91327))))))
  0 91329
  (@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
    (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
    (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) 0
    (@Nat.cast_zero.{0} Real
      (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))))

noncomputable def p12681 :=
p12680
  (@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
    (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
    (@OfNat.ofNat.{0} Real 91329
      (@instOfNatAtLeastTwo.{0} Real 91329 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 91328 (instOfNatNat 91328))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 91327 (instOfNatNat 91327))))))
    91329
    (@Eq.refl.{1} Real
      (@OfNat.ofNat.{0} Real 91329
        (@instOfNatAtLeastTwo.{0} Real 91329
          (@AddMonoidWithOne.toNatCast.{0} Real
            (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
          (Mathlib.Meta.NormNum.instAtLeastTwo 91327)))))

noncomputable def p12682 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (@OfNat.ofNat.{0} Real 100
    (@instOfNatAtLeastTwo.{0} Real 100
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 98)))

noncomputable def p12683 :=
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
    p12543 p12544)

noncomputable def p12684 :=
p12682
  (p12683
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 32
        (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
      Real.pi))

noncomputable def p12685 :=
@Mathlib.Tactic.CancelDenoms.derive_trans.{0} Real Real.instMul
  (p12683
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 32
        (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
      Real.pi))

noncomputable def p12686 :=
@p12685
  (p12683
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 32
        (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
      Real.pi))

noncomputable def p12687 :=
@p12686
  (@OfNat.ofNat.{0} Real 100
    (@instOfNatAtLeastTwo.{0} Real 100
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 98)))

noncomputable def p12688 :=
@congrArg.{1, 1} Real (Real → Real)
  (@HDiv.hDiv.{0, 0, 0} Real Real Real
    (@instHDiv.{0} Real
      (@DivInvMonoid.toDiv.{0} Real
        (@GroupWithZero.toDivInvMonoid.{0} Real
          (@DivisionSemiring.toGroupWithZero.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p12543 p12544)

noncomputable def p12689 :=
@p12688
  (@HDiv.hDiv.{0, 0, 0} Real Real Real
    (@instHDiv.{0} Real
      (@DivInvMonoid.toDiv.{0} Real
        (@GroupWithZero.toDivInvMonoid.{0} Real
          (@DivisionSemiring.toGroupWithZero.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p12543 p12544)

noncomputable def p12690 :=
@congrFun'.{1, 1} Real Real p12683 p12683
  (p12689
    (@HSub.hSub.{0, 0, 0} Real Real Real
      (@instHSub.{0} Real
        (@SubNegMonoid.toSub.{0} Real
          (@AddGroup.toSubNegMonoid.{0} Real
            (@AddGroupWithOne.toAddGroup.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))))))
    (p12556 (@Eq.refl.{1} Real p12544)))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@OfNat.ofNat.{0} Real 32
      (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
    Real.pi)

noncomputable def p12691 :=
@Mathlib.Tactic.CancelDenoms.sub_subst.{0} Real
  (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))
  (@OfNat.ofNat.{0} Real 100
    (@instOfNatAtLeastTwo.{0} Real 100
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 98)))

noncomputable def p12692 :=
@p12691
  (@HDiv.hDiv.{0, 0, 0} Real Real Real
    (@instHDiv.{0} Real
      (@DivInvMonoid.toDiv.{0} Real
        (@GroupWithZero.toDivInvMonoid.{0} Real
          (@DivisionSemiring.toGroupWithZero.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p12543 p12544)

noncomputable def p12693 :=
@p12692
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@OfNat.ofNat.{0} Real 32
      (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
    Real.pi)
  p12560

noncomputable def p12694 :=
@p12693
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real
          (@DivisionSemiring.toSemiring.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p3705 (p12561 Real.pi))

noncomputable def p12695 :=
@Mathlib.Tactic.CancelDenoms.div_subst.{0} Real Real.instField
  (@OfNat.ofNat.{0} Real 1
    (@One.toOfNat1.{0} Real
      (@AddMonoidWithOne.toOne.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))))
  (@OfNat.ofNat.{0} Real 100
    (@instOfNatAtLeastTwo.{0} Real 100
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 98)))

noncomputable def p12696 :=
@p12695
  (@OfNat.ofNat.{0} Real 100
    (@instOfNatAtLeastTwo.{0} Real 100
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 98)))

noncomputable def p12697 :=
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
  p12543

noncomputable def p12698 :=
@HDiv.hDiv.{0, 0, 0} Real Real Real
  (@instHDiv.{0} Real
    (@DivInvMonoid.toDiv.{0} Real
      (@DivisionRing.toDivInvMonoid.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))
  (@OfNat.ofNat.{0} Real 100
    (@instOfNatAtLeastTwo.{0} Real 100
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 98)))

noncomputable def p12699 :=
@Mathlib.Meta.NormNum.isNat_eq_true.{0} Real
  (@Mathlib.Meta.NormNum.instAddMonoidWithOne'.{0} Real
    (@DivisionSemiring.toSemiring.{0} Real
      (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))
  (p12698 p12544)
  (@OfNat.ofNat.{0} Real 1
    (@One.toOfNat1.{0} Real
      (@AddMonoidWithOne.toOne.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))))
  1

noncomputable def p12700 :=
@Mathlib.Meta.NormNum.isNNRat_div.{0} Real
  (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))
  (@OfNat.ofNat.{0} Real 100
    (@instOfNatAtLeastTwo.{0} Real 100
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 98)))

noncomputable def p12701 :=
p12561
  (@Inv.inv.{0} Real
    (@InvOneClass.toInv.{0} Real
      (@DivInvOneMonoid.toInvOneClass.{0} Real
        (@DivisionMonoid.toDivInvOneMonoid.{0} Real
          (@GroupWithZero.toDivisionMonoid.{0} Real
            (@DivisionSemiring.toGroupWithZero.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))))))
    p12544)

noncomputable def p12702 :=
@HMul.hMul.{0, 0, 0} Real Real Real
  (@instHMul.{0} Real (@Distrib.toMul.{0} Real (@instDistribOfSemiring.{0} Real Real.semiring)))
  (@OfNat.ofNat.{0} Real 100
    (@instOfNatAtLeastTwo.{0} Real 100
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 98)))

noncomputable def p12703 :=
p12702
  (@Inv.inv.{0} Real
    (@InvOneClass.toInv.{0} Real
      (@DivInvOneMonoid.toInvOneClass.{0} Real
        (@DivisionMonoid.toDivInvOneMonoid.{0} Real
          (@GroupWithZero.toDivisionMonoid.{0} Real
            (@DivisionSemiring.toGroupWithZero.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))))))
    p12544)

noncomputable def p12704 :=
@Mathlib.Meta.NormNum.isNNRat_mul.{0} Real
  (@DivisionSemiring.toSemiring.{0} Real
    (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real (@Distrib.toMul.{0} Real (@instDistribOfSemiring.{0} Real Real.semiring))))
  (@OfNat.ofNat.{0} Real 100
    (@instOfNatAtLeastTwo.{0} Real 100
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 98)))

noncomputable def p12705 :=
@p12704
  (@Inv.inv.{0} Real
    (@InvOneClass.toInv.{0} Real
      (@DivInvOneMonoid.toInvOneClass.{0} Real
        (@DivisionMonoid.toDivInvOneMonoid.{0} Real
          (@GroupWithZero.toDivisionMonoid.{0} Real
            (@DivisionSemiring.toGroupWithZero.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))))))
    p12544)

noncomputable def p12706 :=
@Mathlib.Meta.NormNum.IsNat.to_isNNRat.{0} Real
  (@DivisionSemiring.toSemiring.{0} Real
    (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))
  (@OfNat.ofNat.{0} Real 100
    (@instOfNatAtLeastTwo.{0} Real 100
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 98)))

noncomputable def p12707 :=
@p12705 100 1 1 1 100 1 100
  (@Eq.refl.{1} (Real → Real → Real)
    (@HMul.hMul.{0, 0, 0} Real Real Real
      (@instHMul.{0} Real (@Distrib.toMul.{0} Real (@instDistribOfSemiring.{0} Real Real.semiring)))))
  (@p12706 100
    (@p12606 100
      (@Eq.refl.{1} Real
        (@OfNat.ofNat.{0} Real 100
          (@instOfNatAtLeastTwo.{0} Real 100
            (@AddMonoidWithOne.toNatCast.{0} Real
              (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 98))))))

noncomputable def p12708 :=
@Mathlib.Meta.NormNum.IsNNRat.to_isNat.{0} Real
  (@DivisionSemiring.toSemiring.{0} Real
    (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))
  (p12698 p12544) 1
  (@p12700 p12544 1 1
    (@Mathlib.Meta.NormNum.IsNat.to_isNNRat.{0} Real
      (@DivisionSemiring.toSemiring.{0} Real
        (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))
      p12701 1
      (@Mathlib.Meta.NormNum.IsNNRat.to_isNat.{0} Real
        (@DivisionSemiring.toSemiring.{0} Real
          (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))
        p12703 1
        (p12707 p12555 (@Eq.refl.{1} Nat (Nat.mul 100 1))
          (@Eq.refl.{1} Nat 100)))))

noncomputable def p12709 :=
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
  (@OfNat.ofNat.{0} Real 100
    (@instOfNatAtLeastTwo.{0} Real 100
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 98)))

noncomputable def p12710 :=
@Mathlib.Meta.NormNum.isNat_eq_true.{0} Real
  (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
  p12709
  (@OfNat.ofNat.{0} Real 100
    (@instOfNatAtLeastTwo.{0} Real 100
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 98)))

noncomputable def p12711 :=
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
  (@OfNat.ofNat.{0} Real 100
    (@instOfNatAtLeastTwo.{0} Real 100
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 98)))

noncomputable def p12712 :=
@p12711 1 100 100
  (@Eq.refl.{1} (Real → Real → Real)
    (@HMul.hMul.{0, 0, 0} Real Real Real
      (@instHMul.{0} Real (@Distrib.toMul.{0} Real (@instDistribOfSemiring.{0} Real Real.semiring)))))
  (p3747
    (@Nat.cast_one.{0} Real
      (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))))
  (@p12606 100
    (@Eq.refl.{1} Real
      (@OfNat.ofNat.{0} Real 100
        (@instOfNatAtLeastTwo.{0} Real 100
          (@AddMonoidWithOne.toNatCast.{0} Real
            (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
          (Mathlib.Meta.NormNum.instAtLeastTwo 98)))))
  (@Eq.refl.{1} Nat 100)

noncomputable def p12713 :=
@p12696 p12543 p12544 p12560
  (@rfl.{1} Real p12697)
  (p12699 p12708
    (p3747
      (@Nat.cast_one.{0} Real
        (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))))
  (@p12710 100 p12712
    (@p12606 100
      (@Eq.refl.{1} Real
        (@OfNat.ofNat.{0} Real 100
          (@instOfNatAtLeastTwo.{0} Real 100
            (@AddMonoidWithOne.toNatCast.{0} Real
              (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 98))))))

noncomputable def p12714 :=
@Mathlib.Tactic.CancelDenoms.mul_subst.{0} Real (@Field.toCommRing.{0} Real Real.instField)
  (@OfNat.ofNat.{0} Real 1
    (@One.toOfNat1.{0} Real
      (@AddMonoidWithOne.toOne.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))))
  (@OfNat.ofNat.{0} Real 100
    (@instOfNatAtLeastTwo.{0} Real 100
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 98)))

noncomputable def p12715 :=
@p12714
  (@OfNat.ofNat.{0} Real 100
    (@instOfNatAtLeastTwo.{0} Real 100
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 98)))

noncomputable def p12716 :=
@p12715
  (@OfNat.ofNat.{0} Real 32
    (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
  Real.pi p3705 (p12561 Real.pi)

noncomputable def p12717 :=
@HMul.hMul.{0, 0, 0} Real Real Real
  (@instHMul.{0} Real
    (@inferInstance.{1} (Mul.{0} Real)
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real
          (@DivisionSemiring.toSemiring.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))))))
  (@OfNat.ofNat.{0} Real 100
    (@instOfNatAtLeastTwo.{0} Real 100
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 98)))

noncomputable def p12718 :=
p12716 (@rfl.{1} Real p3930) (@rfl.{1} Real (p12717 Real.pi))
  (@p12710 100 p12712
    (@p12606 100
      (@Eq.refl.{1} Real
        (@OfNat.ofNat.{0} Real 100
          (@instOfNatAtLeastTwo.{0} Real 100
            (@AddMonoidWithOne.toNatCast.{0} Real
              (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 98))))))

noncomputable def p12719 :=
@Eq.mp.{0}
  (@LT.lt.{0} Real (@Preorder.toLT.{0} Real (@PartialOrder.toPreorder.{0} Real Real.partialOrder))
    p12684
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))))))
  (@LT.lt.{0} Real (@Preorder.toLT.{0} Real (@PartialOrder.toPreorder.{0} Real Real.partialOrder))
    p12562
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))))))
  (@congrArg.{1, 1} Real Prop p12684 p12562
    (fun (_a : Real) =>
      @LT.lt.{0} Real (@Preorder.toLT.{0} Real (@PartialOrder.toPreorder.{0} Real Real.partialOrder)) _a
        (@OfNat.ofNat.{0} Real 0
          (@Zero.toOfNat0.{0} Real
            (@MulZeroClass.toZero.{0} Real
              (@instMulZeroClassOfSemiring.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))))))
    (@p12687 p12562 p12690
      (p12694 p12713 p12718)))

noncomputable def p12720 :=
@Mathlib.Tactic.Linarith.mul_neg.{0} Real Real.instRing Real.partialOrder Real.instIsStrictOrderedRing
  (p12683
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 32
        (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
      Real.pi))

noncomputable def p12721 :=
@Mathlib.Tactic.Linarith.sub_neg_of_lt.{0} Real Real.instRing Real.partialOrder Real.instIsOrderedRing
  (@HDiv.hDiv.{0, 0, 0} Real Real Real
    (@instHDiv.{0} Real
      (@DivInvMonoid.toDiv.{0} Real
        (@GroupWithZero.toDivInvMonoid.{0} Real
          (@DivisionSemiring.toGroupWithZero.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p12543 p12544)

noncomputable def p12722 :=
@Mathlib.Meta.NormNum.isNat_lt_true.{0} Real Real.semiring Real.partialOrder Real.instIsOrderedRing
  (@FloorSemiring.instCharZero.{0} Real (@Ring.toSemiring.{0} Real Real.instRing) Real.partialOrder
    (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing))
  (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
  (@OfNat.ofNat.{0} Real 100
    (@instOfNatAtLeastTwo.{0} Real 100 Real.instNatCast
      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 99 (instOfNatNat 99))
        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 98 (instOfNatNat 98))))))
  0 100
  (@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
    (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
    (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) 0
    (@Nat.cast_zero.{0} Real
      (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))))

noncomputable def p12723 :=
p12722
  (@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
    (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
    (@OfNat.ofNat.{0} Real 100
      (@instOfNatAtLeastTwo.{0} Real 100 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 99 (instOfNatNat 99))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 98 (instOfNatNat 98))))))
    100
    (@Eq.refl.{1} Real
      (@OfNat.ofNat.{0} Real 100
        (@instOfNatAtLeastTwo.{0} Real 100
          (@AddMonoidWithOne.toNatCast.{0} Real
            (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
          (Mathlib.Meta.NormNum.instAtLeastTwo 98)))))

noncomputable def p12724 :=
@Mathlib.Meta.NormNum.isNat_lt_true.{0} Real Real.semiring Real.partialOrder Real.instIsOrderedRing
  (@FloorSemiring.instCharZero.{0} Real (@Ring.toSemiring.{0} Real Real.instRing) Real.partialOrder
    (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing))
  (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
  (@OfNat.ofNat.{0} Real 160
    (@instOfNatAtLeastTwo.{0} Real 160 Real.instNatCast
      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 159 (instOfNatNat 159))
        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 158 (instOfNatNat 158))))))
  0 160
  (@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
    (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
    (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) 0
    (@Nat.cast_zero.{0} Real
      (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))))

noncomputable def p12725 :=
p12724
  (@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
    (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
    (@OfNat.ofNat.{0} Real 160
      (@instOfNatAtLeastTwo.{0} Real 160 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 159 (instOfNatNat 159))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 158 (instOfNatNat 158))))))
    160
    (@Eq.refl.{1} Real
      (@OfNat.ofNat.{0} Real 160
        (@instOfNatAtLeastTwo.{0} Real 160
          (@AddMonoidWithOne.toNatCast.{0} Real
            (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
          (Mathlib.Meta.NormNum.instAtLeastTwo 158)))))

noncomputable def p12726 :=
fun
    (a :
      p12558
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real 32
            (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
          Real.pi)) =>
  @Mathlib.Tactic.Linarith.lt_irrefl.{0} Real Real.instPreorder
    (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
    (p12565 p12676
      (@Mathlib.Tactic.Linarith.add_neg.{0} Real Real.semiring Real.partialOrder Real.instIsStrictOrderedRing
        p12677
        (@HMul.hMul.{0, 0, 0} Real Real Real
          (@instHMul.{0} Real
            (@Distrib.toMul.{0} Real (@instDistribOfSemiring.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))))
          (@OfNat.ofNat.{0} Real 160
            (@instOfNatAtLeastTwo.{0} Real 160 Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 159 (instOfNatNat 159))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 158 (instOfNatNat 158))))))
          p3713)
        (p12678 (p12679 (p12681 (@Eq.refl.{1} Bool false)))
          (p12719
            (@p12720
              (@OfNat.ofNat.{0} Real 100
                (@instOfNatAtLeastTwo.{0} Real 100 Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 99 (instOfNatNat 99))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 98 (instOfNatNat 98))))))
              (@p12721
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real 32
                    (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
                  Real.pi)
                a)
              (p12723 (@Eq.refl.{1} Bool false)))))
        (@Mathlib.Tactic.Linarith.mul_neg.{0} Real Real.instRing Real.partialOrder Real.instIsStrictOrderedRing
          p3713
          (@OfNat.ofNat.{0} Real 160
            (@instOfNatAtLeastTwo.{0} Real 160 Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 159 (instOfNatNat 159))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 158 (instOfNatNat 158))))))
          p3995 (p12725 (@Eq.refl.{1} Bool false)))))

noncomputable def p12727 :=
@Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal d29)
  (hardyZApproximantRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
      true 5))
  true p11263 p11264

noncomputable def p12728 :=
@Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.fstVal d29) p11263
  p11264 p11266 p11267
  (@p12727 p11266 p11267
    (@Eq.refl.{1} Real
      (hardyZApproximantRS
        (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
          true 5)))
    d195)

noncomputable def p12729 :=
@Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal d29)
  (hardyZApproximantRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
      true 5))
  false p11852 p11853

noncomputable def p12730 :=
@Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.sndVal d29) p11852
  p11853 p11855 p11856
  (@p12729 p11855 p11856
    (@Eq.refl.{1} Real
      (hardyZApproximantRS
        (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
          true 5)))
    d204)

noncomputable def p12731 :=
@Zeta.Certificates.ZIntervalRS.Certificate.mk d29
  (@Eq.mpr.{0} p12542 p12545
    (@id.{0} (@Eq.{1} Prop p12542 p12545)
      (@Eq.trans.{1} Prop p12542 p12545 p12545
        (p12547 (p12548 (@Eq.refl.{1} Real p12544)))
        (p12551 (p12556 (@Eq.refl.{1} Real p12544)))))
    (p12557 p12726))
  (BSN.mul_neg_of_neg_pos_r (Zeta.Certificates.ZIntervalRS.fstVal d29)
    (Zeta.Certificates.ZIntervalRS.sndVal d29)
    (p12728 (Eq.refl true) (Eq.refl true) (Eq.refl true))
    (p12730 (Eq.refl true) (Eq.refl true)
      (Eq.refl true)))

noncomputable def p12732 :=
@Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal d29)
  (hardyZErrorBoundRS (@Prod.fst.{0, 0} Real Real (@NonemptyInterval.toProd.{0} Real Real.instLE d29)))
  true false p11263 p11264 p11266

noncomputable def p12733 :=
@p12732 p11267 5972815091 549755813888 201
  549755813888
  (@p12727 p11266 p11267
    (@Eq.refl.{1} Real
      (hardyZApproximantRS
        (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
          true 5)))
    d195)

noncomputable def p12734 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZErrorBoundRS (@Prod.fst.{0, 0} Real Real (@NonemptyInterval.toProd.{0} Real Real.instLE d29)))
  (hardyZErrorBoundRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
      true 5))
  false 5972815091 549755813888

noncomputable def p12735 :=
p12733
  (@p12734 201 549755813888
    (@Eq.refl.{1} Real
      (hardyZErrorBoundRS
        (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101409000
          true 5)))
    d205)

noncomputable def p12736 :=
@Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal d29)
  (hardyZErrorBoundRS (@Prod.snd.{0, 0} Real Real (@NonemptyInterval.toProd.{0} Real Real.instLE d29)))
  false false p11852 p11853 p11855

noncomputable def p12737 :=
@p12736 p11856 5963749889 549755813888 201
  549755813888
  (@p12729 p11855 p11856
    (@Eq.refl.{1} Real
      (hardyZApproximantRS
        (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
          true 5)))
    d204)

noncomputable def p12738 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZErrorBoundRS (@Prod.snd.{0, 0} Real Real (@NonemptyInterval.toProd.{0} Real Real.instLE d29)))
  (hardyZErrorBoundRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
      true 5))
  false 5963749889 549755813888

noncomputable def p12739 :=
p12737
  (@p12738 201 549755813888
    (@Eq.refl.{1} Real
      (hardyZErrorBoundRS
        (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101532300
          true 5)))
    d206)

theorem d207 : Zeta.Certificates.ZIntervalRS.Certificate d29 :=
p12731
  (p12735 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (p12739 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
end RHHeight1000.GramZero659

theorem solution : ∃ t ∈ Set.Ioo (1014.09000 : ℝ) (1015.32300 : ℝ), riemannZeta (1 / 2 + Complex.I * t) = 0 := by
  exact riemannZeta.exists_zero_of_zIntervalRS_certificate _ RHHeight1000.GramZero659.d207
