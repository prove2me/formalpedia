-- Prove2me | solution 1 for RHHeight1000.gram_zero663_exists
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-19T16:54:55.693231+00:00
-- url     : https://prove2.me/submissions/e0c64c5c-842e-436d-bb3e-90caa6824756

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

namespace RHHeight1000.GramZero663
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

noncomputable abbrev c9 := (@InnerProductSpace.toNormedSpace Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal Real Real.instRCLike))

noncomputable abbrev c10 := (@Nat.rawCast Nat
      (@AddCommMonoidWithOne.toAddMonoidWithOne Nat
        (@NonAssocSemiring.toAddCommMonoidWithOne Nat
          (@Semiring.toNonAssocSemiring Nat (@CommSemiring.toSemiring Nat Nat.instCommSemiring))))
      1)

noncomputable abbrev c11 := (@DenselyNormedField.toNontriviallyNormedField Real Real.denselyNormedField)

noncomputable abbrev c12 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) Real.pi Real.pi)

noncomputable abbrev c13 := (@DivisionSemiring.toSemiring NNRat (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield))

noncomputable abbrev c14 := (@Neg.neg Real
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

noncomputable abbrev c15 := (@OfNat.ofNat Real 918231
    (@instOfNatAtLeastTwo Real 918231
      (@AddMonoidWithOne.toNatCast Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne Real
          (@NonAssocSemiring.toAddCommMonoidWithOne Real (@Semiring.toNonAssocSemiring Real Real.semiring))))
      (@Nat.instAtLeastTwoHAddOfNat
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) 918229
          (@OfNat.ofNat Nat 1 (instOfNatNat 1)))
        (@instNeZeroNatHAdd_1 918229 (@OfNat.ofNat Nat 1 (instOfNatNat 1))
          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 0 (instOfNatNat 0)))))))

noncomputable abbrev c16 := (@OfNat.ofNat Real 1600
    (@instOfNatAtLeastTwo Real 1600
      (@AddMonoidWithOne.toNatCast Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne Real
          (@NonAssocSemiring.toAddCommMonoidWithOne Real (@Semiring.toNonAssocSemiring Real Real.semiring))))
      (@Nat.instAtLeastTwoHAddOfNat
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) 1598
          (@OfNat.ofNat Nat 1 (instOfNatNat 1)))
        (@instNeZeroNatHAdd_1 1598 (@OfNat.ofNat Nat 1 (instOfNatNat 1))
          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 0 (instOfNatNat 0)))))))

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

noncomputable abbrev c30 := (@OfNat.ofNat Real 918231
      (@instOfNatAtLeastTwo Real 918231 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 918230 (instOfNatNat 918230))
          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 918229 (instOfNatNat 918229))))))

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

noncomputable abbrev c35 := (@instHAdd Real (@AddSemigroup.toAdd Real (@AddMonoid.toAddSemigroup Real Real.instAddMonoid)))

noncomputable abbrev c36 := (@NegZeroClass.toNeg Real
      (@SubNegZeroMonoid.toNegZeroClass Real
        (@SubtractionMonoid.toSubNegZeroMonoid Real
          (@SubtractionCommMonoid.toSubtractionMonoid Real
            (@AddCommGroup.toDivisionAddCommMonoid Real Real.instAddCommGroup)))))

noncomputable abbrev c37 := (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))

noncomputable abbrev c38 := (@OfNat.ofNat Real 1600
            (@instOfNatAtLeastTwo Real 1600 Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 1599 (instOfNatNat 1599))
                (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 1598 (instOfNatNat 1598))))))

noncomputable abbrev c39 := (@OfNat.ofNat Real 1
    (@One.toOfNat1 Real
      (@AddMonoidWithOne.toOne Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne Real
          (@NonAssocSemiring.toAddCommMonoidWithOne Real (@Semiring.toNonAssocSemiring Real Real.semiring))))))

noncomputable abbrev c40 := (@OfNat.ofNat Real 918231
    (@instOfNatAtLeastTwo Real 918231 Real.instNatCast
      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 918230 (instOfNatNat 918230))
        (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 918229 (instOfNatNat 918229))))))

noncomputable abbrev c41 := (@Nat.cast Real Real.instNatCast 9007199254740992)

noncomputable abbrev c42 := (@Nat.cast Real Real.instNatCast 1125899906842624)

noncomputable abbrev c43 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8)))

noncomputable abbrev c44 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))

noncomputable abbrev c45 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

noncomputable abbrev c46 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

noncomputable abbrev c47 := (@OfNat.ofNat Real 20
    (@instOfNatAtLeastTwo Real 20 Real.instNatCast
      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 19 (instOfNatNat 19))
        (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 18 (instOfNatNat 18))))))

noncomputable abbrev c48 := (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield)

noncomputable abbrev c49 := (@Zero.toOfNat0 Real (@MulZeroClass.toZero Real (@instMulZeroClassOfSemiring Real Real.semiring)))

noncomputable abbrev c50 := (@OfNat.ofNat Real 0
          (@Zero.toOfNat0 Real
            (@MulZeroClass.toZero Real
              (@instMulZeroClassOfSemiring Real (@Ring.toSemiring Real Real.instRing)))))

noncomputable abbrev c51 := (@Distrib.toMul Real (@instDistribOfSemiring Real (@Ring.toSemiring Real Real.instRing)))

noncomputable abbrev c52 := (@instHSub Real
    (@SubNegMonoid.toSub Real
      (@AddGroup.toSubNegMonoid Real
        (@AddGroupWithOne.toAddGroup Real (@Ring.toAddGroupWithOne Real Real.instRing)))))

noncomputable abbrev c53 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 12)))

noncomputable abbrev c54 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 11)))

noncomputable abbrev c55 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 10)))

noncomputable abbrev c56 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9)))

noncomputable abbrev c57 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7)))

noncomputable abbrev c58 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6)))

noncomputable abbrev c59 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

noncomputable abbrev c60 := (@Nat.cast Real Real.instNatCast 42040055262383233)

noncomputable abbrev c61 := (@Nat.cast Real Real.instNatCast 5200563471780473)

noncomputable abbrev c62 := (@instHDiv Real
    (@DivInvMonoid.toDiv Real
      (@DivisionRing.toDivInvMonoid Real (@Field.toDivisionRing Real Real.instField))))

noncomputable abbrev c63 := (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 998 (instOfNatNat 998)))

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
@Mathlib.Meta.NormNum.isNNRat_inv_pos NNRat c48
  NNRat.instCharZero
  (@Nat.cast NNRat
    c6
    100000)
  99999

noncomputable def p10 :=
@Mathlib.Meta.NormNum.IsNat.to_isNNRat NNRat
  c13
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
          c13)))
    100000 100000 (Mathlib.Meta.NormNum.IsNat.raw_refl 100000))

noncomputable def p341 :=
@Mathlib.Meta.NormNum.isRat_le_true Real
  c32 Real.linearOrder
  Real.instIsStrictOrderedRing
  (@OfScientific.ofScientific Real c2 101903100
    true 5)
  (@OfScientific.ofScientific Real c2 102026300
    true 5)
  (Int.ofNat 1019031) (Int.ofNat 1020263) 1000

noncomputable def p342 :=
@Mathlib.Meta.NormNum.isNNRat_nnratCast Real
  c3
  (@FloorSemiring.instCharZero Real Real.semiring Real.partialOrder
    c26)
  (NNRat.divNat 101903100
    (@HPow.hPow Nat Nat Nat
      c27
      (@OfNat.ofNat Nat 10 (instOfNatNat 10)) 5))
  1019031 1000

noncomputable def p343 :=
@Mathlib.Meta.NormNum.isNNRat_divNat 101903100 101903100 1019031
  (@HPow.hPow Nat Nat Nat
    c27
    (@OfNat.ofNat Nat 10 (instOfNatNat 10)) 5)
  100000 1000 (Mathlib.Meta.NormNum.IsNat.raw_refl 101903100)

noncomputable def p344 :=
@Mathlib.Meta.NormNum.isNNRat_div NNRat c48
  (@Nat.cast NNRat
    c6
    101903100)
  (@Nat.cast NNRat
    c6
    100000)

noncomputable def p345 :=
@Mathlib.Meta.NormNum.isNNRat_mul NNRat
  c13
  (@HMul.hMul NNRat NNRat NNRat
    (@instHMul NNRat
      (@Distrib.toMul NNRat
        (@instDistribOfSemiring NNRat
          c13))))
  (@Nat.cast NNRat
    c6
    101903100)
  (@Inv.inv NNRat
    c28
    (@Nat.cast NNRat
      (@AddMonoidWithOne.toNatCast NNRat
        (@AddCommMonoidWithOne.toAddMonoidWithOne NNRat
          (@NonAssocSemiring.toAddCommMonoidWithOne NNRat
            (@Semiring.toNonAssocSemiring NNRat
              c13))))
      100000))

noncomputable def p346 :=
@Mathlib.Meta.NormNum.IsNat.to_isNNRat NNRat
  c13
  (@Nat.cast NNRat
    c6
    101903100)
  101903100

noncomputable def p347 :=
p346
  (@Mathlib.Meta.NormNum.isNat_natCast NNRat
    (@AddCommMonoidWithOne.toAddMonoidWithOne NNRat
      (@NonAssocSemiring.toAddCommMonoidWithOne NNRat
        (@Semiring.toNonAssocSemiring NNRat
          c13)))
    101903100 101903100 (Mathlib.Meta.NormNum.IsNat.raw_refl 101903100))

noncomputable def p348 :=
@p345 101903100 1 1019031 1 100000 1000
  100
  (@Eq.refl (NNRat → NNRat → NNRat)
    (@HMul.hMul NNRat NNRat NNRat
      (@instHMul NNRat
        (@Distrib.toMul NNRat
          (@instDistribOfSemiring NNRat
            c13)))))
  p347 (@p9 1 p11)

noncomputable def p349 :=
@p341 1000
  (@Mathlib.Meta.NormNum.IsNNRat.to_isRat Real
    c32
    (@OfScientific.ofScientific Real c2 101903100
      true 5)
    1019031 1000
    (@Mathlib.Meta.NormNum.isNNRat_ofScientific_of_true Real
      c3 101903100
      5 1019031 1000
      (p342
        (p343 p4
          (@p344 1019031 1000
            (p348 (@Eq.refl Nat (Nat.mul 101903100 1))
              (@Eq.refl Nat 100000)))))))

noncomputable def p350 :=
@Mathlib.Meta.NormNum.isNNRat_nnratCast Real
  c3
  (@FloorSemiring.instCharZero Real Real.semiring Real.partialOrder
    c26)
  (NNRat.divNat 102026300
    (@HPow.hPow Nat Nat Nat
      c27
      (@OfNat.ofNat Nat 10 (instOfNatNat 10)) 5))
  1020263 1000

noncomputable def p351 :=
@Mathlib.Meta.NormNum.isNNRat_divNat 102026300 102026300 1020263
  (@HPow.hPow Nat Nat Nat
    c27
    (@OfNat.ofNat Nat 10 (instOfNatNat 10)) 5)
  100000 1000 (Mathlib.Meta.NormNum.IsNat.raw_refl 102026300)

noncomputable def p352 :=
@Mathlib.Meta.NormNum.isNNRat_div NNRat c48
  (@Nat.cast NNRat
    c6
    102026300)
  (@Nat.cast NNRat
    c6
    100000)

noncomputable def p353 :=
@Mathlib.Meta.NormNum.isNNRat_mul NNRat
  c13
  (@HMul.hMul NNRat NNRat NNRat
    (@instHMul NNRat
      (@Distrib.toMul NNRat
        (@instDistribOfSemiring NNRat
          c13))))
  (@Nat.cast NNRat
    c6
    102026300)
  (@Inv.inv NNRat
    c28
    (@Nat.cast NNRat
      (@AddMonoidWithOne.toNatCast NNRat
        (@AddCommMonoidWithOne.toAddMonoidWithOne NNRat
          (@NonAssocSemiring.toAddCommMonoidWithOne NNRat
            (@Semiring.toNonAssocSemiring NNRat
              c13))))
      100000))

noncomputable def p354 :=
@Mathlib.Meta.NormNum.IsNat.to_isNNRat NNRat
  c13
  (@Nat.cast NNRat
    c6
    102026300)
  102026300

noncomputable def p355 :=
p354
  (@Mathlib.Meta.NormNum.isNat_natCast NNRat
    (@AddCommMonoidWithOne.toAddMonoidWithOne NNRat
      (@NonAssocSemiring.toAddCommMonoidWithOne NNRat
        (@Semiring.toNonAssocSemiring NNRat
          c13)))
    102026300 102026300 (Mathlib.Meta.NormNum.IsNat.raw_refl 102026300))

noncomputable def p356 :=
@p353 102026300 1 1020263 1 100000 1000
  100
  (@Eq.refl (NNRat → NNRat → NNRat)
    (@HMul.hMul NNRat NNRat NNRat
      (@instHMul NNRat
        (@Distrib.toMul NNRat
          (@instDistribOfSemiring NNRat
            c13)))))
  p355 (@p9 1 p11)

noncomputable def p357 :=
p349
  (@Mathlib.Meta.NormNum.IsNNRat.to_isRat Real
    c32
    (@OfScientific.ofScientific Real c2 102026300
      true 5)
    1020263 1000
    (@Mathlib.Meta.NormNum.isNNRat_ofScientific_of_true Real
      c3 102026300
      5 1020263 1000
      (p350
        (p351 p4
          (@p352 1020263 1000
            (p356 (@Eq.refl Nat (Nat.mul 102026300 1))
              (@Eq.refl Nat 100000)))))))

theorem d56 : @LE.le Real
  (@Preorder.toLE Real
    (@PartialOrder.toPreorder Real
      (@SemilatticeInf.toPartialOrder Real
        (@Lattice.toSemilatticeInf Real
          (@DistribLattice.toLattice Real (@instDistribLatticeOfLinearOrder Real Real.linearOrder))))))
  (@OfScientific.ofScientific Real c2 101903100
    true 5)
  (@OfScientific.ofScientific Real c2 102026300
    true 5) :=
p357 (Eq.refl true)

noncomputable def d57 :=
@NonemptyInterval.mk Real Real.instLE
  (@Prod.mk Real Real
    (@OfScientific.ofScientific Real c2 101903100
      true 5)
    (@OfScientific.ofScientific Real c2 102026300
      true 5))
  d56

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
Enclosure.Real.IsNear c46
  false 759250125 1073741824 1 8589934592

noncomputable def p2077 :=
@Enclosure.Real.IsNear.recentre'
  c46 false
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
Enclosure.Real.IsNear c46
  false 97184016000 137438953472 16 137438953472

noncomputable def p2084 :=
@Enclosure.Real.IsNear.recentre'
  c46 false
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
Enclosure.Real.IsNear c45
  false 4959401049 8589934592 1 8589934592

noncomputable def p2093 :=
@Enclosure.Real.IsNear.recentre'
  c45 false
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
Enclosure.Real.IsNear c45
  false 79350416784 137438953472 16 137438953472

noncomputable def p2100 :=
@Enclosure.Real.IsNear.recentre'
  c45 false
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
Enclosure.Real.IsNear c59
  false 8589934591 17179869184 1 17179869184

noncomputable def p2159 :=
@Enclosure.Real.IsNear.recentre'
  c59 false
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
Enclosure.Real.IsNear c59
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
Enclosure.Real.IsNear c44
  false 1920767767 4294967296 1 8589934592

noncomputable def p2183 :=
@Enclosure.Real.IsNear.recentre'
  c44 false
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
Enclosure.Real.IsNear c44
  false 61464568544 137438953472 16 137438953472

noncomputable def p2190 :=
@Enclosure.Real.IsNear.recentre'
  c44 false
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
Enclosure.Real.IsNear c58
  false 7013652225 17179869184 1 17179869184

noncomputable def p2201 :=
@Enclosure.Real.IsNear.recentre'
  c58 false
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
Enclosure.Real.IsNear c58
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
Enclosure.Real.IsNear c57
  false 6493380203 17179869184 1 17179869184

noncomputable def p2218 :=
@Enclosure.Real.IsNear.recentre'
  c57 false
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
Enclosure.Real.IsNear c57
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
Enclosure.Real.IsNear c43
  false 759250125 2147483648 1 8589934592

noncomputable def p2234 :=
@Enclosure.Real.IsNear.recentre'
  c43 false
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
Enclosure.Real.IsNear c43
  false 48592008000 137438953472 16 137438953472

noncomputable def p2241 :=
@Enclosure.Real.IsNear.recentre'
  c43 false
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
Enclosure.Real.IsNear c56
  false 5726623061 17179869184 1 17179869184

noncomputable def p2251 :=
@Enclosure.Real.IsNear.recentre'
  c56 false
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
Enclosure.Real.IsNear c56
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
Enclosure.Real.IsNear c55
  false 5432751653 17179869184 1 17179869184

noncomputable def p2267 :=
@Enclosure.Real.IsNear.recentre'
  c55 false
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
Enclosure.Real.IsNear c55
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
Enclosure.Real.IsNear c54
  false 5179925457 17179869184 1 17179869184

noncomputable def p2283 :=
@Enclosure.Real.IsNear.recentre'
  c54 false
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
Enclosure.Real.IsNear c54
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
Enclosure.Real.IsNear c53
  false 4959401049 17179869184 1 17179869184

noncomputable def p2299 :=
@Enclosure.Real.IsNear.recentre'
  c53 false
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
Enclosure.Real.IsNear c53
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
Enclosure.Real.IsNear c12 false
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
    c12)
  false p1068 p1070

noncomputable def p2321 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 4 1)
  c12 4 1
  0 1

noncomputable def p2323 :=
Enclosure.Real.IsNear
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 8 1)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      c12 Real.pi))
  false

noncomputable def p2324 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 8 1)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    c12 Real.pi)
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
@Enclosure.Real.IsNear.mulLit_ff c12
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
    c12)
  p2332 p2333 p2334

noncomputable def p2336 :=
nat_lit 134217728000000000000000000000000000000

noncomputable def p2337 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 96 1)
  c12 96 1
  0 1

noncomputable def p2422 :=
nat_lit 26400000000000000000000000

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

noncomputable def p2704 :=
nat_lit 633825300114114700748351602688

noncomputable def p2848 :=
nat_lit 69992023193056381579920071267763883691301421788582797965624659405118495974380029543152421664737722368

noncomputable def p2930 :=
nat_lit 374144419156711147060143317175368453031918731001856

noncomputable def p3100 :=
nat_lit
  22411863820821928299396788597249255122883414756292876443347498757095858352850426348339495190732159462721908983095900632933469148367597566755911644326690509857065670593740800

noncomputable def p3103 :=
nat_lit
  784415233728767490478887600903723929300919516470250675517162456498355042349764922191882331675625581195266814408356522152671420192865914836456907551434167844997298470780928000

noncomputable def p3287 :=
nat_lit
  1204861799007386865375571354988119955406212377298305037594361533181473345049238920486731261453760892715929826931235618026503301416242045188797809999002881809915850451119505408000

noncomputable def p3290 :=
nat_lit
  184343855248130190402462417313182353177150493726640670751937314576765421792533554834469883002425416585537263520479049558055005116685032913886064929847440916917125119021284327424000

noncomputable def p3344 :=
nat_lit 158456325028528675187087900672

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
  c39
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
  c39
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
    c10)
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
    c10)
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
    c10
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
    c10
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
  c52
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
@Mathlib.Meta.NormNum.isNNRat_div NNRat c48
  (@Nat.cast NNRat
    c6
    315)
  (@Nat.cast NNRat
    c6
    100)

noncomputable def p3952 :=
@Mathlib.Meta.NormNum.isNNRat_mul NNRat
  c13
  (@HMul.hMul NNRat NNRat NNRat
    (@instHMul NNRat
      (@Distrib.toMul NNRat
        (@instDistribOfSemiring NNRat
          c13))))
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
              c13))))
      100))

noncomputable def p3953 :=
@Mathlib.Meta.NormNum.IsNat.to_isNNRat NNRat
  c13
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
          c13)))
    315 315 (Mathlib.Meta.NormNum.IsNat.raw_refl 315))

noncomputable def p3955 :=
@Mathlib.Meta.NormNum.isNNRat_inv_pos NNRat c48
  NNRat.instCharZero
  (@Nat.cast NNRat
    c6
    100)
  99

noncomputable def p3956 :=
@Mathlib.Meta.NormNum.IsNat.to_isNNRat NNRat
  c13
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
          c13)))
    100 100 (Mathlib.Meta.NormNum.IsNat.raw_refl 100))

noncomputable def p3958 :=
@p3952 315 1 63 1 100 20 5
  (@Eq.refl (NNRat → NNRat → NNRat)
    (@HMul.hMul NNRat NNRat NNRat
      (@instHMul NNRat
        (@Distrib.toMul NNRat
          (@instDistribOfSemiring NNRat
            c13)))))
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
        c50)
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
  c47

noncomputable def p3993 :=
@Mathlib.Meta.NormNum.isNat_lt_true Real Real.semiring Real.partialOrder Real.instIsOrderedRing
  (@FloorSemiring.instCharZero Real (@Ring.toSemiring Real Real.instRing) Real.partialOrder
    c26)
  c25
  c47
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

noncomputable def p4831 :=
nat_lit 69206016000000000000000000

noncomputable def p4996 :=
nat_lit 951160241300648755200000000

noncomputable def p5018 :=
nat_lit 73786976294838206464000000000000000

noncomputable def p5674 :=
nat_lit
  3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713438470702986642486608412251521024

noncomputable def p5990 :=
nat_lit 25711008708143844408671393477458601640355247900524685364822016000000000

noncomputable def p5994 :=
nat_lit 87112285931760246646623899502532662132736000000

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

noncomputable def p6053 :=
@HMul.hMul Real Real Real
  c19
  c16

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
    c10)
  (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (Int.negOfNat 32000))

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
    c10)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    32000)

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
    c10)
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
    c10
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
    c10
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
    c10
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
        c34))
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
  p6120 c65

noncomputable def p6131 :=
@Mathlib.Tactic.Ring.Common.mul_congr Real Real.instCommSemiring
  c16

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
  c16

noncomputable def p6135 :=
@Mathlib.Meta.NormNum.isNat_ofNat Real
  c5
  c16

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
    c10
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
        c34))
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

noncomputable def p6171 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  (@OfNat.ofNat Real 1000
    (@instOfNatAtLeastTwo Real 1000
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 998)))

noncomputable def p6180 :=
@Mathlib.Tactic.CancelDenoms.sub_subst Real
  c32
  (@OfNat.ofNat Real 1000
    (@instOfNatAtLeastTwo Real 1000
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 998)))

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

noncomputable def p6187 :=
@HDiv.hDiv Real Real Real
  c62
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

noncomputable def p6211 :=
@Mathlib.Meta.NormNum.isNat_lt_true Real Real.semiring Real.partialOrder Real.instIsOrderedRing
  (@FloorSemiring.instCharZero Real (@Ring.toSemiring Real Real.instRing) Real.partialOrder
    c26)
  c25
  (@OfNat.ofNat Real 1000
    (@instOfNatAtLeastTwo Real 1000 Real.instNatCast
      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 999 (instOfNatNat 999))
        c63)))
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
          c63)))
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

noncomputable def p6907 :=
nat_lit 4835703278458516698824704000000000000000

noncomputable def p7486 :=
nat_lit 842498333348457493583344221469363458551160763204392890034487820288

noncomputable def p8045 :=
nat_lit 2239744742177804210557442280568444278121645497234649534899989100963791871180160945380877493271607115776

noncomputable def p8228 :=
nat_lit 17422457186352049329324779900506532426547200000

noncomputable def p10041 :=
nat_lit 253530120045645880299340641075200000000000000

noncomputable def p12328 :=
nat_lit
  115402833396154575366545869793535889621349127769526229668542875625964151543596233127717554347659978665736274395563047822181610776723872051477952309687675478936779750458329093309163388859169570944610465113807304808518412809535488000

noncomputable def p12330 :=
nat_lit
  17656633509611650031081518078410991112066416548737513139287059970772515186170223668540785815191976735857649982521146316793786448838752423876126703382214348277327301820124351276301998495452944354525401162412517635703317159858929664000

noncomputable def p13788 :=
nat_lit
  418993997810706159361688281193932691483730181893512293053861295116305125939798343025058571817715732115313495568327689089179808837873330310826051531440128

noncomputable def p14431 :=
nat_lit 1267650600228229401496703205376

noncomputable def p15946 :=
nat_lit 242833611528216133864932738352939863330300854881517440156476551217363035650651062272

noncomputable def p16711 :=
nat_lit 13479973333575319897333507543509815336818572211270286240551805124608

noncomputable def p16796 :=
nat_lit 5142201741628768881734278695491720328071049580104937072964403200000000

noncomputable def p18030 :=
nat_lit 60708402882054033466233184588234965832575213720379360039119137804340758912662765568

theorem d237 : Enclosure.Real.IsNear Real.pi false 226375608064910080 72057594037927936 1
  1000000000000000 :=
BSN.pi_near_15

theorem d238 : p2306 500000000000000 :=
@p501 1 1000000000000000 884279719003555 140737488355328
  1 500000000000000 (Enclosure.Real.IsNear.const false 2 1)
  d237 (Eq.refl true)

noncomputable def p18265 :=
Enclosure.Real.IsNear
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi))
  false 179192535600709 1125899906842624

noncomputable def p18266 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi))
  false 179192535600709 1125899906842624

noncomputable def p18267 :=
@p18266 1 1125899906842624 179192535600709 1125899906842624
  1 1125899906842624
  (@p2309 89596267800354 89596267800355 562949953421312 d238
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))

theorem d239 : p18265 1 1125899906842624 :=
p18267 (Eq.refl true)

theorem d240 : p2314 250000000000000 :=
@p2315 1 1000000000000000 884279719003555 70368744177664
  1 250000000000000 (Enclosure.Real.IsNear.const false 4 1)
  d237 (Eq.refl true)

theorem d241 : p2317 p2318 :=
@p2319 p2316 p1071 p2318 d237
  d237 (Eq.refl true)

noncomputable def p18268 :=
@p2321 p1068 p2316 p1071 p2318
  p1068 p1070 p1071 p1072
  (Enclosure.Real.IsNear.const false 4 1) d241 (Eq.refl true)

theorem d242 : p2320 p1071 p1072 :=
p18268

noncomputable def p18269 :=
@p2328 p2318 226375608064910080 72057594037927936 1
  1000000000000000 p1059 p2325 p1062
  p2326 d241 d237

theorem d243 : p2323 p1059 p1061 p1062 p1063 :=
p2327 (p18269 (Eq.refl true)) (Eq.refl true)

noncomputable def p18270 :=
Enclosure.Real.IsNear
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 96 1)
      c12))
  false 1188307408585

noncomputable def p18271 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 96 1)
      c12))
  false 1188307408585

noncomputable def p18272 :=
@p2337 p1068 p2316 p1071 p2318
  p2332 p2333 p2334 p2336
  (Enclosure.Real.IsNear.const false 96 1) d241 (Eq.refl true)

noncomputable def p18273 :=
@p2335 p2336 594153704292 594153704293 562949953421312
  p18272 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

theorem d244 : p18270 1125899906842624 1 1125899906842624 :=
@p18271 1125899906842624 1 1125899906842624 1188307408585
  1125899906842624 1 1125899906842624 p18273
  (Eq.refl true)

noncomputable def p18275 :=
nat_lit
  74751027079122046462216955587793573067050655862760405902609490213261724339546970300512875500623813013973275600053770769378323738155015176163371603062328757260320680744718580942157810765768356265984

noncomputable def p18475 :=
nat_lit
  4351082437154956072465106588077822995084026820419845514849846380137705962380101572519219218556758308199541387151331336317719177934050977705242787666055883587123865770683541250307916824576

noncomputable def p18566 :=
nat_lit
  253266331108459042877954581524118722595974501479640924072000569439126758509088631982403994686712878069348015540240526683495797795130113239006767262824338603946605334680267915264

noncomputable def p18574 :=
nat_lit
  224945689727159819140526925384299092943484855915095831655037778630591879033574393515952034305194542857496045531676044756160413302774714984450425759043258192756736

noncomputable def p18592 :=
nat_lit
  199791907220223502808422222706762643567910281130558153654986045416023791284464999687699590596063486154228923591770023865308670443474450259602571264

noncomputable def p18612 :=
nat_lit 162259276829213363391578010288128

noncomputable def p18616 :=
nat_lit
  43925764306044571680725368323646467224816202519423813658702209381811720879245495124946621119333294851884583971973988952045017884473517666335936773745853447711512838489228428960142291910923747779038711709484005529634972877481305336765315945935580498848143981594566316233845365667885724853864409164021094426004311404627406132328947657274877275719882979792982905046104421923507813744640000

noncomputable def p18619 :=
nat_lit
  10146851554696296058247560082762333928932542781986900955160210367198507523105709373862669478565991110785338897525991447922399131313382580923601394735292146421359465691011767089792869431423385736957942404890805277345678734698181532792787983511119095233921259748344819050018279469281602441242678516888872812406995934468930816567986908830496650691292968332179051065650121464330304975011840000

noncomputable def p18666 :=
nat_lit 497323236409786642155382248146820840100456150797347717440463976893159497012533375533056

noncomputable def p18672 :=
nat_lit 6277101735386680763835789423207666416102355444464034512896

noncomputable def p18691 :=
nat_lit 121748510886483040665600000000

noncomputable def p18695 :=
nat_lit 178405961588244985132285746181186892047843328

noncomputable def p18697 :=
nat_lit 5444517870735015415413993718908291383296000000000000000

noncomputable def p18713 :=
nat_lit
  2371728904138043385318735560374504222700605579872037175997883585289299297944925459400262945270439995320386160994569494400873352117161187529222914467416668525224467727137180455887633346091077280717708110065332645507572399051088361938793378954328561156096000

noncomputable def p18716 :=
nat_lit
  135188547535868472963167926941346740693934518052706119031879364361490059982860751185814987880415079733262011176690461180849781070678187689165706124642750105937794660446819285985595100727191405000909362273723960793931626745912036630511222600396727985897472000

noncomputable def p18725 :=
nat_lit 5575186299632655785383929568162090376495104

noncomputable def p18739 :=
nat_lit
  26068754422020242755335860258679067180644360935168211642010495233358709885485065609561450188402496767899127163308765923818732185965496218501019777765128248418025372493348965463231703293438828334554344859193466359040392401283092440636892428972474131770237648762755971780096283208066310154669126010645890362914782576640000

noncomputable def p18742 :=
nat_lit
  6021882271486676076482583719754864518728847376023856889304424398905861983547050155808694993520976753384698374724324928402127134958029626473735568663744625384563861045963611022006523460784369345282053662473690728938330644696394353787122151092641524438924896864196629481202241421063317645728568108459200673833314775203840000

noncomputable def p18754 :=
nat_lit
  1260864198284623334792929283204595641762551656654894293374345388935863096687910739565256520156317300505812095689818112

noncomputable def p18760 :=
nat_lit 15583809393469829205196800000000000000000000000

noncomputable def p18769 :=
nat_lit
  227166498108393291591690474249109426965528421018278839661455426590473243066834650624926416047854179247596172938820614485527445924608820872880385787908168637421617142754592441181269508473347051925777211342581761153821293384735107078859788885002196634811247029175151612501537270086431278076342027182518829056000

noncomputable def p18772 :=
nat_lit
  12948490392178417620726357032199237337035119998041893860702959315656974854809575085620805714727688217112981857512775025675064417702702789754181989910765612333032177137011769147332361982980781959769301046527160385767813722929901103495007966445125208184241080662983641912587624394926582850351495549403573256192000

noncomputable def p18825 :=
nat_lit 14134776518227074636666380005943348126619871175004951664972849610340958208

noncomputable def p18881 :=
nat_lit 3138550867693340381917894711603833208051177722232017256448

noncomputable def p19930 :=
nat_lit
  29318946348370735950614953471724902892035659778686303370924035973403351920680196650828649657041572109220866795685663090828463014466074168711287689728830129530405087447123273447861751046106886250777

noncomputable def p19931 :=
nat_lit
  18687756769780511615554238896948393266762663965690101475652372553315431084886742575128218875155953253493318900013442692344580934538753794040842900765582189315080170186179645235539452691442089066496

noncomputable def p19932 :=
Enclosure.Real.IsNear
  (hardyZApproximantRS
    (@OfScientific.ofScientific Real c2 101903100
      true 5))
  true p19930 p19931

noncomputable def p19933 :=
nat_lit
  3246947496404399361547513364548015491499109768317605901260102757514869110694223234478678307386264586584535440585809007640022356353376488727506033411821721191563384988082966385705280442190279537407325054472681956241529046211255201998363338142202809

noncomputable def p19934 :=
nat_lit
  977714390151285340458550700767136717512176682191527488009085245149149233651877928154962655543168043857028866984041619938209700576166989005586407679348640825296100732777858093547520000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p19935 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZApproximantRS
    (@OfScientific.ofScientific Real c2 101903100
      true 5))
  (hardyZApproximantRS
    (@OfScientific.ofScientific Real c2 101903100
      true 5))
  true p19930

noncomputable def p19936 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
  (Zeta.RiemannSiegel.mainSumOfPhase
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101903100
        true 5))
    (@OfScientific.ofScientific Real c2 101903100
      true 5)
    12)

noncomputable def p19937 :=
@HPow.hPow Real Real Real (@instHPow Real Real Real.instPow)
  (@HDiv.hDiv Real Real Real c4
    (@OfScientific.ofScientific Real c2 101903100
      true 5)
    c7)

noncomputable def p19938 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  c22
  (p19937
    (@Neg.neg Real Real.instNeg
      (@HDiv.hDiv Real Real Real c4
        c37
        c20)))

noncomputable def p19939 :=
Real.sqrt
  (@HDiv.hDiv Real Real Real c4
    (@OfScientific.ofScientific Real c2 101903100
      true 5)
    c7)

noncomputable def p19940 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p19938
  (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
        (Enclosure.sfrac false 12 1)))
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Zeta.RiemannSiegel.correctionLinear
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
          (Enclosure.sfrac false 12 1)))
      (@Inv.inv Real Real.instInv p19939)))

noncomputable def p19941 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZApproximantRS
    (@OfScientific.ofScientific Real c2 101903100
      true 5))
  (p19936 p19940) true p19930

noncomputable def p19942 :=
@BSN.floor_sqrt_eq_dec
  (@OfScientific.ofScientific Real c2 101903100
    true 5)
  101903100 100000 12
  (Enclosure.sfrac_ofScientific_eq 101903100 5 100000 (Eq.refl true))

noncomputable def p19943 :=
@Enclosure.Real.IsNear.subLit_tf
  (Zeta.RiemannSiegel.mainSumOfPhase
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101903100
        true 5))
    (@OfScientific.ofScientific Real c2 101903100
      true 5)
    12)

noncomputable def p19944 :=
nat_lit
  2539134523526882610646059963561610526075320237998191684007294168348702893989913782004913095691524124369440474366308934995103687124014573591972028870696781225019871500545711059190999626246964977945

noncomputable def p19945 :=
nat_lit
  132280282464149534596844079407560187034359794827315570704741256743672336496362142111294777262294484050470818083828969978563102761298195110041087848415992240942021454108888945705280442190279537407325054472681956241529046211255201998363338142202809

noncomputable def p19946 :=
nat_lit
  125923915719430933791342696249620118630068977615240270821253291806094922316100230690157781576835168321529362928242236871182526193077363456125367093432720514672533688217414588739031381872322864567479269588992

noncomputable def p19947 :=
@p19943 p19940 6154747057 4294967296 218917
  68719476736 p19944 p19931 p19945
  p19934 p19946 p19930

noncomputable def p19948 :=
@Enclosure.Real.IsNear.of_eq
  (Zeta.RiemannSiegel.mainSumOfPhase
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101903100
        true 5))
    (@OfScientific.ofScientific Real c2 101903100
      true 5)
    12)

noncomputable def p19949 :=
@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101903100
        true 5))
    (@OfScientific.ofScientific Real c2 101903100
      true 5)
    12)

noncomputable def p19950 :=
p19949
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101903100
        true 5))
    (@OfScientific.ofScientific Real c2 101903100
      true 5)
    12)

noncomputable def p19951 :=
@p19948 p19950 true 6154747057 4294967296 218917
  68719476736
  (BSN.main_sum_of_phase_eq
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101903100
        true 5))
    (@OfScientific.ofScientific Real c2 101903100
      true 5)
    12)

noncomputable def p19952 :=
@Enclosure.Real.IsNear.addLit_tt
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101903100
        true 5))
    (@OfScientific.ofScientific Real c2 101903100
      true 5)
    12)

noncomputable def p19953 :=
@p19952
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101903100
        true 5))
    (@OfScientific.ofScientific Real c2 101903100
      true 5)
    12)

noncomputable def p19954 :=
@p19953 98475952912 137438953472 218917 137438953472
  98475952912 137438953472 218917 137438953472 27068863820766461820928
  6154747057 4294967296

noncomputable def p19955 :=
BSN.mainSumRS_step
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real c2 101903100
      true 5))
  (@OfScientific.ofScientific Real c2 101903100
    true 5)
  Real.cos BSN.quadSignNeg

noncomputable def p19956 :=
p19955 11 12 101903100 100000 286
  137438953472 68719476736 2305843009213693952 false 286268686541415
  3376

noncomputable def p19957 :=
p19956 341522969406 43 39675208392 8 true
  58898824521 205283 true 9665959457 7244019458077122842 1

noncomputable def p19958 :=
p19957 false 137099194379 true true 98475952912 218917
  BSN.abs_quadSignNeg (BSN.cos_quad_nat2 286 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 137099194379 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101903100 5 100000 (Eq.refl true))
  (Eq.refl true)

noncomputable def p19959 :=
BSN.mainSumRS_step2
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real c2 101903100
      true 5))
  (@OfScientific.ofScientific Real c2 101903100
    true 5)
  Real.sin Real.sin

noncomputable def p19960 :=
p19959 BSN.quadSignPos BSN.quadSignNeg 9 10 11 101903100
  100000 167 229 137438953472 68719476736

noncomputable def p19961 :=
p19960 2305843009213693952 false 286268686541415 3376
  316464885454 43 43462013224 8 329564216814 43
  41439403656

noncomputable def p19962 :=
p19961 8 true 66039967812 176110 true 165445401177
  true 128976733403 7244019458077122842 1 false

noncomputable def p19963 :=
p19962 128285503389 false false 110862478192 true true
  58898824521 205283 BSN.abs_quadSignPos
  (BSN.cos_quad_nat3 167 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 128285503389 137438953472)

noncomputable def p19964 :=
p19959 BSN.quadSignPos BSN.quadSignPos 7 8 9 101903100
  100000 23 99 137438953472 68719476736

noncomputable def p19965 :=
p19964 2305843009213693952 false 286268686541415 3376
  285796269294 43 48592008000 16 301984246446 43
  45812984488

noncomputable def p19966 :=
p19965 8 true 94249704945 143665 true 1133678255
  true 89650374735 7244019458077122842 1 false

noncomputable def p19967 :=
p19966 1133665399 false false 83426777668 false true
  66039967812 176110 BSN.abs_quadSignPos
  (BSN.cos_quad_nat3 23 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 1133665399 137438953472)

noncomputable def p19968 :=
p19959 BSN.quadSignPos BSN.quadSignPos 5 6 7 101903100
  100000 163 63 137438953472 68719476736

noncomputable def p19969 :=
p19968 2305843009213693952 false 286268686541415 3376
  246257546308 43 56109217800 8 267443854420 43
  51947041624

noncomputable def p19970 :=
p19969 8 true 183889295204 106540 false 134770536234
  false 134126121789 7244019458077122842 1 false

noncomputable def p19971 :=
p19970 114187433299 false false 113827539068 false true
  94249704945 143665 BSN.abs_quadSignPos
  (BSN.cos_quad_nat3 163 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 114187433299 137438953472)

noncomputable def p19972 :=
BSN.mainSumRS_step2
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real c2 101903100
      true 5))
  (@OfScientific.ofScientific Real c2 101903100
    true 5)
  Real.cos Real.sin

noncomputable def p19973 :=
p19972 BSN.quadSignNeg BSN.quadSignNeg 3 4 5 101903100
  100000 426 281 137438953472 68719476736

noncomputable def p19974 :=
p19973 2305843009213693952 false 286268686541415 3376
  190530846192 42 68719476728 8 221199462352 42
  61464568544

noncomputable def p19975 :=
p19974 16 true 88512310187 62774 false 143302821512
  false 194879701863 7244019458077122842 1 false

noncomputable def p19976 :=
p19975 69258228433 true false 135836368605 true true
  183889295204 106540 BSN.abs_quadSignNeg
  (BSN.cos_quad_nat2 426 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 69258228433 137438953472)

noncomputable def p19977 :=
p19972 BSN.quadSignPos BSN.quadSignNeg 1 2 3 101903100
  100000 876 613 137438953472 68719476736

noncomputable def p19978 :=
p19977 2305843009213693952 false 286268686541415 3376
  95265423088 42 97184016000 16 150992123216 42
  79350416784

noncomputable def p19979 :=
p19978 16 true 137438375456 3426 false 71850720046
  false 63318422539 7244019458077122842 1 false

noncomputable def p19980 :=
p19979 119081659400 false false 61102220767 true true
  88512310187 62774 BSN.abs_quadSignPos
  (BSN.cos_quad_nat0 876 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 119081659400 137438953472)

noncomputable def p19981 :=
@Enclosure.Real.IsNear.recentre'
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101903100
        true 5))
    (@OfScientific.ofScientific Real c2 101903100
      true 5)
    1)

noncomputable def p19982 :=
@Enclosure.Real.IsNear.of_eq
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101903100
        true 5))
    (@OfScientific.ofScientific Real c2 101903100
      true 5)
    1)

noncomputable def p19983 :=
@p19982
  (Real.cos
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101903100
        true 5)))
  true 4294949233

noncomputable def p19984 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101903100
        true 5)))
  true 17179796932

noncomputable def p19985 :=
@Enclosure.Real.IsNear.cos_image
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real c2 101903100
      true 5))
  (@HDiv.hDiv Real Real Real c4
    (@Nat.cast Real Real.instNatCast 8945896454419)
    (@Nat.cast Real Real.instNatCast 4294967296))
  false 8945896454419

noncomputable def p19986 :=
nat_lit 1680615838411430405958017134545086910789874757029825804041

noncomputable def p19987 :=
nat_lit 806871631020384686467430208196334624696082043670364160

noncomputable def p19988 :=
@Enclosure.Real.IsNear.recentre'
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real c2 101903100
      true 5))
  false p19986 p19987

noncomputable def p19989 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 101903100 400000)
      (Real.log (Enclosure.sfrac false 41536977158440000 160000000000)))
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 1 4)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 1 2) Real.pi)
        (Real.arctan
          (@HDiv.hDiv Real Real Real c4
            (@Nat.cast Real Real.instNatCast 100000)
            (@Nat.cast Real Real.instNatCast 203806200))))))

noncomputable def p19990 :=
nat_lit 527446581329823417281285963592480000000000000000

noncomputable def p19991 :=
nat_lit 3224906865632465170804220321872706921280000000000000

noncomputable def p19992 :=
@Enclosure.Real.IsNear.of_eq
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real c2 101903100
      true 5))
  (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (p19989 (Enclosure.sfrac false 101903100 200000))
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 101903100 200000) (Real.log Real.pi)))
    (Enclosure.sfrac true p19990 p19991))
  false

noncomputable def p19993 :=
BSN.riemannSiegelThetaApproximant_two_zero_mk
  (@OfScientific.ofScientific Real c2 101903100
    true 5)
  101903100 100000 41536977158440000 160000000000

noncomputable def p19994 :=
p19993 203806200 400000 200000 p19990
  p19991
  (Enclosure.sfrac_ofScientific_eq 101903100 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p19995 :=
@Enclosure.Real.IsNear.addLit_ft_p
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (p19989 (Enclosure.sfrac false 101903100 200000))
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 101903100 200000) (Real.log Real.pi)))
  (Enclosure.sfrac true p19990 p19991) 1500872489147368395561
  720575940379279360

noncomputable def p19996 :=
nat_lit 4840173614624919569159089347489850303074839300245898315638080000000000000

noncomputable def p19997 :=
@p19995 1699620586974233483 p4831 p19990
  p19991 0 1 p19996 p19986
  p19987 1699620586974233483 p4831

noncomputable def p19998 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (p19989 (Enclosure.sfrac false 101903100 200000))
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 101903100 200000) (Real.log Real.pi))
  48028847431737044410113 18014398509481984000 1284360442891
  132000000000000000000

noncomputable def p19999 :=
nat_lit 5156958605083249746718789258444800000

noncomputable def p20000 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 101903100 400000)
      (Real.log (Enclosure.sfrac false 41536977158440000 160000000000)))
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 1 4)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 1 2) Real.pi)
        (Real.arctan
          (@HDiv.hDiv Real Real Real c4
            (@Nat.cast Real Real.instNatCast 100000)
            (@Nat.cast Real Real.instNatCast 203806200))))))

noncomputable def p20001 :=
@p20000 (Enclosure.sfrac false 101903100 200000)
  11441492539099002445773 3602879701896396800 1284360442891
  132000000000000000000 101903100 200000 0

noncomputable def p20002 :=
nat_lit 1921153897269481776404520000

noncomputable def p20003 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 101903100 400000)
    (Real.log (Enclosure.sfrac false 41536977158440000 160000000000)))
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 1 4)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 1 2) Real.pi)
      (Real.arctan
        (@HDiv.hDiv Real Real Real c4
          (@Nat.cast Real Real.instNatCast 100000)
          (@Nat.cast Real Real.instNatCast 203806200)))))
  11442906944700314245773

noncomputable def p20004 :=
nat_lit 25763950767824288775310697268410056704

noncomputable def p20005 :=
@p20003 3602879701896396800 424786808797 44000000000000000000
  884003500819875 2251799813685248 20000033 264000000000000000
  p20004 11441492539099002445773 3602879701896396800 1284360442891

noncomputable def p20006 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 101903100 400000)
  (Real.log (Enclosure.sfrac false 41536977158440000 160000000000)) 101903100
  400000 0 1 56146019820301415 4503599627370496

noncomputable def p20007 :=
nat_lit 30866600822881583908803051520

noncomputable def p20008 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv Real Real Real c4
      (@Nat.cast Real Real.instNatCast 41536977158440000)
      (@Nat.cast Real Real.instNatCast 160000000000)))
  false p20007 p2333

noncomputable def p20009 :=
BSN.log_rat_reduce_isNear 41536977158440000 160000000000 17 83073954316880000
  41943040000000000 46964176802 68719476736 24973259072661432
  36028797018963968 26400000000 1000000000000000

noncomputable def p20010 :=
nat_lit
  1024868219348682837231381935055479403682882893287064315263211389383982598414605517292025199225222922637947679303465682240751709577709954164376301609015515433680358512756953619133586464460267793923951676438847022135116357481596655852863124666350021107727887635373095634365327352859938925838336000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p20011 :=
nat_lit
  39582575041757317284699523238190852122637947006494851037525844095925052363437439673961206408025359033880684386028798793090419876513329836243117500468394101624091065404914669548508268373233935518653547230847750778272525306938554236082886284702355648526723514224107780915254225333257116424601600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p20012 :=
nat_lit
  1064939705490198338356782637474364364011873133281915850604681698519755046342067925726096863271958773687073627373963103316163650046082326862498165353996536487530972996767491438645822692972286487778962222209461693027458546973152072535087666566261498204695034571496141450229141471232000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p20013 :=
BSN.log_dyadic_bound 20565457158440000 62508497158440000 12 11
  p20010 68719476736 26400000000 p20011 p20012
  46964176802 83073954316880000

noncomputable def p20014 :=
p20013 41943040000000000 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p20015 :=
@BSN.binarySplit_of_base11 (BSN.artanhP 20565457158440000) (BSN.artanhQ 62508497158440000)
  0 11 p20011 p20010 p20012
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p20016 :=
p20009 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p20014 (p20015 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

noncomputable def p20017 :=
@p20006 1250561 33000000000000000 11442906944700314245773
  3602879701896396800 424786808797 44000000000000000000
  (Enclosure.Real.IsNear.const false 101903100 400000)
  (BSN.isNear_log_sfrac 41536977158440000 160000000000 56146019820301415
    4503599627370496 1250561 33000000000000000 false
    (@p20008 1000448800000000 p2422 56146019820301415
      4503599627370496 1250561 33000000000000000
      (p20016 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p20018 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 1 4)
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 1 2) Real.pi)
    (Real.arctan
      (@HDiv.hDiv Real Real Real c4
        (@Nat.cast Real Real.instNatCast 100000)
        (@Nat.cast Real Real.instNatCast 203806200))))
  1 4

noncomputable def p20019 :=
@p20018 0 1 884003500819875 562949953421312 20000033
  66000000000000000 884003500819875 2251799813685248 20000033
  264000000000000000 (Enclosure.Real.IsNear.const false 1 4)

noncomputable def p20020 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 1 2) Real.pi)
  (Real.arctan
    (@HDiv.hDiv Real Real Real c4
      (@Nat.cast Real Real.instNatCast 100000) (@Nat.cast Real Real.instNatCast 203806200)))
  884279719003555 562949953421312 1

noncomputable def p20021 :=
nat_lit 7593532251141744623616000

noncomputable def p20022 :=
@p20020 2000000000000000 4214755 8589934592 1
  3300000000 p20021 884003500819875 562949953421312 20000033
  66000000000000000
  (@p803 1 1000000000000000 884279719003555 562949953421312
    1 2000000000000000 (Enclosure.Real.IsNear.const false 1 2)
    BSN.pi_near_15 (Eq.refl true))

noncomputable def p20023 :=
BSN.arctan_dyadic_bound_f 100000 203806200 1 0 8589934592
  3300000000 0 1 1 0 1

noncomputable def p20024 :=
p20023 1 4214755 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)
  (@BSN.binarySplit_of_le (BSN.arctanEvenP 100000) (BSN.arctanEvenQ 203806200) 0
    0 (Eq.refl true))
  (@BSN.binarySplit_of_le (BSN.arctanOddP 100000) (BSN.arctanOddQ 203806200) 0 0
    (Eq.refl true))

noncomputable def p20025 :=
p20019
  (p20022
    (p20024 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p20026 :=
@p19998 80162316917822529 137438953472000 1019031
  68719476736000 p19999 1500872489147368395561 720575940379279360
  1699620586974233483 p4831
  (@p20001 1 p20002 48028847431737044410113
    18014398509481984000 1284360442891 132000000000000000000
    (@p20005 132000000000000000000 p20017 p20025
      (Eq.refl true) (Eq.refl true))
    (Enclosure.Real.IsNear.const false 101903100 200000) (Eq.refl true)
    (Eq.refl true))

noncomputable def p20027 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 101903100 200000) (Real.log Real.pi)
  101903100 200000 0 1 78665238759 68719476736

noncomputable def p20028 :=
p20026
  (@p20027 1 34359738368 80162316917822529 137438953472000
    1019031 68719476736000
    (Enclosure.Real.IsNear.const false 101903100 200000) d91
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p20029 :=
@p19985 4294967296 423 17179869184 true 17179796932
  17179869184 1 3300000000
  (@p19988 1699620586974233483 p4831 8945896454419
    4294967296 423 17179869184
    (@p19992 p19986 p19987 1699620586974233483
      p4831
      (p19994 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p19997 (p20028 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p19990 p19991)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p20030 :=
nat_lit 1795145029493120395378688

noncomputable def p20031 :=
BSN.cos_reduce2
  (@HDiv.hDiv Real Real Real c4
    (@Nat.cast Real Real.instNatCast 8945896454419)
    (@Nat.cast Real Real.instNatCast 4294967296))
  (@HDiv.hDiv Real Real Real c4
    (@Nat.cast Real Real.instNatCast p20030)
    (@Nat.cast Real Real.instNatCast p504))
  226375608064910080 72057594037927936 false

noncomputable def p20032 :=
BSN.sin_reduce_arg_pos_rat_q2 8945896454419 4294967296 226375608064910080
  72057594037927936 331 p20030 p504
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p20033 :=
BSN.cos_dyadic_bound_f 102042180827 35184372088832 1 0 17179869184
  6606445313 0 1 1 0 1

noncomputable def p20034 :=
p20033 1 17179796932 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (@BSN.binarySplit_of_le (BSN.cosEvenP 102042180827) (BSN.cosEvenQ 35184372088832) 0
    0 (Eq.refl true))

noncomputable def p20035 :=
p20034
  (@BSN.binarySplit_of_le (BSN.cosOddP 102042180827) (BSN.cosOddQ 35184372088832) 0
    0 (Eq.refl true))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p20036 :=
@BSN.cos_arg_round false 17179796932 17179869184 p20030
  p504 102042180827 35184372088832 6606445313 6600000000
  p20035 (Eq.refl true)

noncomputable def p20037 :=
p20031 17179796932 17179869184 331 1000000000000000
  6600000000 3300000000 p20032 BSN.pi_near_15 p20036
  (Eq.refl true) (Eq.refl true)

noncomputable def p20038 :=
@p19983 4294967296 5519843239 221459251200000000
  (BSN.main_sum_rs_one
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101903100
        true 5))
    (@OfScientific.ofScientific Real c2 101903100
      true 5))
  (@p19984 17179869184 1413079869184 56693568307200000000
    4294949233 4294967296 5519843239 221459251200000000
    (p20029 (Enclosure.sfrac_false_div 8945896454419 4294967296)
      (p20037 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p20039 :=
@p19981 true 4294949233 4294967296 5519843239
  221459251200000000 137438375456 137438953472 3426 137438953472
  p20038 (Eq.refl true)

noncomputable def p20040 :=
p19980 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 613 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 61102220767 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101903100 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true) p20039
  (@p19988 1699620586974233483 p4831 286268686541415
    137438953472 3376 137438953472
    (@p19992 p19986 p19987 1699620586974233483
      p4831
      (p19994 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p19997 (p20028 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p19990 p19991)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p20041 :=
nat_lit 15976897446837023867955428244911510237532464983048962764414509479259081809681419739756380416

noncomputable def p20042 :=
nat_lit 710311748461030245807622478364571384942430231328684364554771364391267249522329176391936

noncomputable def p20043 :=
nat_lit 47929271717014149543374669489777801569827510088684230924514418895048462894545214560916357376

noncomputable def p20044 :=
BSN.cos_dyadic_bound_f 71850720046 137438953472 3 2 137438953472
  68719476736 p20041 p2466 p20042
  p20043 p2469

noncomputable def p20045 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP 71850720046) (BSN.cosEvenQ 137438953472) 0
  2 p20041 p2466 p20042 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20046 :=
p20044 p20042 119081659400 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p20045 (Eq.refl true))

noncomputable def p20047 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP 71850720046) (BSN.cosOddQ 137438953472) 0
  2 p20043 p2469 p20042 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20048 :=
nat_lit 17343947948185151794753878291432298996918439634259124919916986946928318690720436515260447585

noncomputable def p20049 :=
nat_lit 258369172030021506716246312893932934690699205217259040548074149028588019777178135280481

noncomputable def p20050 :=
nat_lit 45424207266587348951439759697816097671939747433870213513716935598094788380807218299177384801

noncomputable def p20051 :=
BSN.sin_dyadic_bound_f 63318422539 137438953472 3 2 137438953472
  68719476736 p20048 p2477 p20049
  p20050 p2480

noncomputable def p20052 :=
@BSN.binarySplit_of_base2 (BSN.sinEvenP 63318422539) (BSN.sinEvenQ 137438953472) 0
  2 p20048 p2477 p20049 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20053 :=
p20051 p20049 61102220767 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p20052 (Eq.refl true))

noncomputable def p20054 :=
@BSN.binarySplit_of_base2 (BSN.sinOddP 63318422539) (BSN.sinOddQ 137438953472) 0
  2 p20050 p2480 p20049 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20055 :=
p20040 d93 d95 d97 d99 d103
  (p20046 (p20047 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p20053 (p20054 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p20056 :=
p19976 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 281 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 135836368605 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101903100 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p20055 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p19988 1699620586974233483 p4831 286268686541415
    137438953472 3376 137438953472
    (@p19992 p19986 p19987 1699620586974233483
      p4831
      (p19994 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p19997 (p20028 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p19990 p19991)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p20057 :=
nat_lit
  1072330991913034684868325219051653887628498830720833106643257097280531227917470394298730869367897479989992952021022013357326257119853633601536

noncomputable def p20058 :=
nat_lit
  74999245867312111170682779658381008952800919879235376259189094570396556051652135638405511495049191339555537892132159485487357158752256

noncomputable def p20059 :=
nat_lit
  6502425338116969412601437243219268459308207202629374411822044570518714609459172892336295000490528918771046729680811702328773528415855957770240

noncomputable def p20060 :=
BSN.cos_dyadic_bound_f 143302821512 137438953472 4 3 137438953472
  68719476736 p20057 p2457 p20058
  p20059 p2460

noncomputable def p20061 :=
@BSN.binarySplit_of_base3 (BSN.cosEvenP 143302821512) (BSN.cosEvenQ 137438953472) 0
  3 p20057 p2457 p20058 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20062 :=
p20060 p20058 69258228433 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p20061 (Eq.refl true))

noncomputable def p20063 :=
@BSN.binarySplit_of_base3 (BSN.cosOddP 143302821512) (BSN.cosOddQ 137438953472) 0
  3 p20059 p2460 p20058 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20064 :=
nat_lit
  9541672333494412308254050024716950218324000991583588233089784908517427970596805002465109078112105815373760879133782924316033751306342328267681

noncomputable def p20065 :=
nat_lit
  3000539018059648344039062885907599066507531020066465903664931017508257436924400028080891793198315020096514081060556055547079798332158881

noncomputable def p20066 :=
nat_lit
  47668978730561140810890809172850711583606110940340324046657389923047227319317579955428209712773270047006233503136882526932334830062897461031841

noncomputable def p20067 :=
BSN.sin_dyadic_bound_f 194879701863 137438953472 4 3 137438953472
  68719476736 p20064 p2504 p20065
  p20066 p2507

noncomputable def p20068 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 194879701863) (BSN.sinEvenQ 137438953472) 0
  3 p20064 p2504 p20065 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20069 :=
p20067 p20065 135836368605 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p20068 (Eq.refl true))

noncomputable def p20070 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 194879701863) (BSN.sinOddQ 137438953472) 0
  3 p20066 p2507 p20065 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20071 :=
p20056 d105 d107 d109 d111 d103
  (p20062 (p20063 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p20069 (p20070 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p20072 :=
p19971 BSN.abs_quadSignPos (BSN.cos_quad_nat3 63 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 113827539068 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101903100 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p20071 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p19988 1699620586974233483 p4831 286268686541415
    137438953472 3376 137438953472
    (@p19992 p19986 p19987 1699620586974233483
      p4831
      (p19994 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p19997 (p20028 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p19990 p19991)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p20073 :=
nat_lit
  2180170115937616060792402055789910550421073222262458564379754712648391871235985528282310449860666928913230828624203904538770562173359383187456

noncomputable def p20074 :=
nat_lit
  35903722323522590841400195286206236705597710764996331066433983761534567694955141898660425043224832298835295794570621081571937719750656

noncomputable def p20075 :=
nat_lit
  10898790742923243614717853160062760826433607723064907460097329021047209023881866305461220825646191357169736836860284418962709827163415835119616

noncomputable def p20076 :=
BSN.sin_dyadic_bound_f 134770536234 137438953472 4 3 137438953472
  68719476736 p20073 p2504 p20074
  p20075 p2507

noncomputable def p20077 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 134770536234) (BSN.sinEvenQ 137438953472) 0
  3 p20073 p2504 p20074 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20078 :=
p20076 p20074 114187433299 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p20077 (Eq.refl true))

noncomputable def p20079 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 134770536234) (BSN.sinOddQ 137438953472) 0
  3 p20075 p2507 p20074 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20080 :=
nat_lit
  2138757300917710235276002157226198387829367806153544071677450262984119828862267944869427775965708209183045111627897933345391140061113868500721

noncomputable def p20081 :=
nat_lit
  33896933200284747221758661108379304714700205788737586002472002692740026499446715198319248801359681393389662478320759937703300581179121

noncomputable def p20082 :=
nat_lit
  10691804158319659771345960490389377429823995281226293162593255186603486150549252212738606384419661720785955087863227122713712933703571815677681

noncomputable def p20083 :=
BSN.sin_dyadic_bound_f 134126121789 137438953472 4 3 137438953472
  68719476736 p20080 p2504 p20081
  p20082 p2507

noncomputable def p20084 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 134126121789) (BSN.sinEvenQ 137438953472) 0
  3 p20080 p2504 p20081 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20085 :=
p20083 p20081 113827539068 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p20084 (Eq.refl true))

noncomputable def p20086 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 134126121789) (BSN.sinOddQ 137438953472) 0
  3 p20082 p2507 p20081 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20087 :=
p20072 d113 d115 d117 d119 d103
  (p20078 (p20079 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p20085 (p20086 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p20088 :=
p19967 BSN.abs_quadSignPos (BSN.cos_quad_nat3 99 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 83426777668 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101903100 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p20087 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p19988 1699620586974233483 p4831 286268686541415
    137438953472 3376 137438953472
    (@p19992 p19986 p19987 1699620586974233483
      p4831
      (p19994 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p19997 (p20028 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p19990 p19991)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p20089 :=
BSN.sin_dyadic_bound_f 1133678255 137438953472 1 0 137438953472
  68719476736 0 1 1 0 1

noncomputable def p20090 :=
p20089 1 1133665399 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (@BSN.binarySplit_of_le (BSN.sinEvenP 1133678255) (BSN.sinEvenQ 137438953472) 0
    0 (Eq.refl true))

noncomputable def p20091 :=
p20090
  (@BSN.binarySplit_of_le (BSN.sinOddP 1133678255) (BSN.sinOddQ 137438953472) 0
    0 (Eq.refl true))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p20092 :=
nat_lit 69703659763352666678498240716512769484224815381620954995917300835834664310527531173265930625

noncomputable def p20093 :=
nat_lit 4172697233296489350997169309309169896009168757848500163155162944229341474221957562890625

noncomputable def p20094 :=
nat_lit 182550448346593551746641396935794562374090501631018365512852584306228701879470984189166090625

noncomputable def p20095 :=
BSN.sin_dyadic_bound_f 89650374735 137438953472 3 2 137438953472
  68719476736 p20092 p2477 p20093
  p20094 p2480

noncomputable def p20096 :=
@BSN.binarySplit_of_base2 (BSN.sinEvenP 89650374735) (BSN.sinEvenQ 137438953472) 0
  2 p20092 p2477 p20093 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20097 :=
p20095 p20093 83426777668 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p20096 (Eq.refl true))

noncomputable def p20098 :=
@BSN.binarySplit_of_base2 (BSN.sinOddP 89650374735) (BSN.sinOddQ 137438953472) 0
  2 p20094 p2480 p20093 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20099 :=
p20088 d121 d123 d125 d127 d103
  p20091
  (p20097 (p20098 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true) (Eq.refl true)

noncomputable def p20100 :=
p19963 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 229 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 110862478192 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101903100 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p20099 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true))
  (@p19988 1699620586974233483 p4831 286268686541415
    137438953472 3376 137438953472
    (@p19992 p19986 p19987 1699620586974233483
      p4831
      (p19994 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p19997 (p20028 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p19990 p19991)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p20101 :=
nat_lit
  4953339367896897306953272096680969835754703359720801528511608149063103204417546974555778652372230109229535163083206412282306777426536458281121

noncomputable def p20102 :=
nat_lit
  420587534642867885914910732127285151666268199671743095568402251902154168199756858191789879841421553128959610329422342936192849202831521

noncomputable def p20103 :=
nat_lit
  24756071342814115328458744880885865312998142462043362926436776561599021442741914739211616206884324567700022578910713280162367831863865099346081

noncomputable def p20104 :=
BSN.sin_dyadic_bound_f 165445401177 137438953472 4 3 137438953472
  68719476736 p20101 p2504 p20102
  p20103 p2507

noncomputable def p20105 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 165445401177) (BSN.sinEvenQ 137438953472) 0
  3 p20101 p2504 p20102 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20106 :=
p20104 p20102 128285503389 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p20105 (Eq.refl true))

noncomputable def p20107 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 165445401177) (BSN.sinOddQ 137438953472) 0
  3 p20103 p2507 p20102 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20108 :=
nat_lit
  1828667099808106181311703506132021094548791332019894866854009289476741165162715893072450860589513987519617161720394539596571233619298078233041

noncomputable def p20109 :=
nat_lit
  21190269504474773794088451659934730668254981112062853118618954774305497444271209252874160970728719807080389134399938732769383140889041

noncomputable def p20110 :=
nat_lit
  9141886195809126889358603810670414970321498434058729476284339414834829978856449318526276490025722579604345283186262534688581144521785184424401

noncomputable def p20111 :=
BSN.sin_dyadic_bound_f 128976733403 137438953472 4 3 137438953472
  68719476736 p20108 p2504 p20109
  p20110 p2507

noncomputable def p20112 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 128976733403) (BSN.sinEvenQ 137438953472) 0
  3 p20108 p2504 p20109 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20113 :=
p20111 p20109 110862478192 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p20112 (Eq.refl true))

noncomputable def p20114 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 128976733403) (BSN.sinOddQ 137438953472) 0
  3 p20110 p2507 p20109 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20115 :=
p20100 d129 d131 d133 d135 d103
  (p20106 (p20107 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p20113 (p20114 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p20116 :=
p19958
  (p20115 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p19988 1699620586974233483 p4831 286268686541415
    137438953472 3376 137438953472
    (@p19992 p19986 p19987 1699620586974233483
      p4831
      (p19994 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p19997 (p20028 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p19990 p19991)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p20117 :=
nat_lit 8729309198441685408007627297271169052801

noncomputable def p20118 :=
BSN.cos_dyadic_bound_f 9665959457 137438953472 2 1 137438953472
  68719476736 p20117 p2486 p20117
  p20117 p2487

noncomputable def p20119 :=
@BSN.binarySplit_of_base (BSN.cosEvenP 9665959457) (BSN.cosEvenQ 137438953472) 0
  1 p20117 p2486 p20117 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20120 :=
p20118 p20117 137099194379 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p20119 (Eq.refl true))

noncomputable def p20121 :=
@BSN.binarySplit_of_base (BSN.cosOddP 9665959457) (BSN.cosOddQ 137438953472) 0 1
  p20117 p2487 p20117 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20122 :=
p20116 d137 d139 d103
  (p20120 (p20121 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true) (Eq.refl true)

noncomputable def p20123 :=
@p19947 p19931 p19933 p19934
  (p19951
    (@p19954 218917 68719476736
      (p20122 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (p20122 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true) (Eq.refl true)))

noncomputable def p20124 :=
@Enclosure.Real.IsNear.mulLit_ff p19938
  (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
        (Enclosure.sfrac false 12 1)))
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Zeta.RiemannSiegel.correctionLinear
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
          (Enclosure.sfrac false 12 1)))
      (@Inv.inv Real Real.instInv p19939)))

noncomputable def p20125 :=
nat_lit
  2109734141614398454867427424046032048200924587076789621887077122944460920788938594360039757193287048990845002813578121977279904786331895098468600587732799539066931725092933214321218078047

noncomputable def p20126 :=
nat_lit
  878913003928859341525687377113532437201884805294005343789039195766298577140984120613064971479634978663310233816283217107725480411399794700426054617669188901876423367801310748252603817089600646192711282203342941544175856356174338530270889

noncomputable def p20127 :=
nat_lit
  1821134966148595028479677998958410169020624239354445576684708232337886902786563948085462032897710881860980516269880570356193372190309667970214798449256719695955702537256960000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p20128 :=
@p20124 1203532935 4294967296 1 8589934592
  p20125 p18475 p20126 p20127
  p19944 p19931 p19945

noncomputable def p20129 :=
@Enclosure.Real.IsNear.mulLit_ff
  c22
  (p19937
    (@Neg.neg Real Real.instNeg
      (@HDiv.hDiv Real Real Real c4
        c37
        c20)))

noncomputable def p20130 :=
@p20129 1 1 0 1 1203532935 4294967296
  1 8589934592 1203532935 4294967296 1

noncomputable def p20131 :=
@Enclosure.Real.IsNear.of_eq
  (p19937
    (@Neg.neg Real Real.instNeg
      (@HDiv.hDiv Real Real Real c4
        c37
        c20)))

noncomputable def p20132 :=
BSN.rpow_neg_quarter_mk
  (@HDiv.hDiv Real Real Real c4
    (@OfScientific.ofScientific Real c2 101903100
      true 5)
    c7)

noncomputable def p20133 :=
p20132
  (BSN.t_div_two_pi_nonneg
    (@OfScientific.ofScientific Real c2 101903100
      true 5)
    101903100 100000
    (Enclosure.sfrac_ofScientific_eq 101903100 5 100000 (Eq.refl true)))

noncomputable def p20134 :=
@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt p19939)) false
  4814131740 17179869184 2 17179869184 1203532935 4294967296

noncomputable def p20135 :=
@Enclosure.Real.IsNear.recentre' (Real.sqrt p19939) false 61308647361
  17179869184 7 17179869184 61308647361 17179869184 7
  17179869184

noncomputable def p20136 :=
@Enclosure.Real.IsNear.sqrt_image
  (@HDiv.hDiv Real Real Real c4
    (@OfScientific.ofScientific Real c2 101903100
      true 5)
    c7)

noncomputable def p20137 :=
@Enclosure.Real.IsNear.of_eq
  (@HDiv.hDiv Real Real Real c4
    (@OfScientific.ofScientific Real c2 101903100
      true 5)
    c7)

noncomputable def p20138 :=
@p20137
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 101903100 100000)
    (@Inv.inv Real Real.instInv
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)))
  false 2786296826051193

noncomputable def p20139 :=
@p20138 17179869184000 1019031 17179869184000
  (BSN.t_div_two_pi_mk
    (@OfScientific.ofScientific Real c2 101903100
      true 5)
    101903100 100000
    (Enclosure.sfrac_ofScientific_eq 101903100 5 100000 (Eq.refl true)))

noncomputable def p20140 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 101903100 100000)
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi))
  101903100 100000 0

noncomputable def p20141 :=
@p20140 1 2734261103 17179869184 1 17179869184
  2786296826051193 17179869184000 1019031 17179869184000
  (Enclosure.Real.IsNear.const false 101903100 100000) d142

noncomputable def p20142 :=
@p20136 2786296826051193 17179869184000 1019031 17179869184000
  109394029729 109394029770 8589934592
  (p20139 (p20141 (Eq.refl true))) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20143 :=
@Enclosure.Real.IsNear.recentre' p19939 false 218788059499 17179869184
  41 17179869184 218788059499 17179869184 41 17179869184
  (p20142 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p20144 :=
@Enclosure.Real.IsNear.sqrt_image p19939 218788059499 17179869184 41
  17179869184 30654323677 30654323684 8589934592
  (p20143 (Eq.refl true)) (Eq.refl true) (Eq.refl true)

noncomputable def p20145 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt p19939) 61308647361 17179869184
  7 17179869184 2407065869 2407065871 8589934592
  (p20135
    (p20144 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p20146 :=
@p20131 (@Inv.inv Real Real.instInv (Real.sqrt p19939)) false
  1203532935 4294967296 1 8589934592 p20133
  (@p20134 1 8589934592
    (p20145 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p20147 :=
@Enclosure.Real.IsNear.addLit_ft_p
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
      (Enclosure.sfrac false 12 1)))
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Zeta.RiemannSiegel.correctionLinear
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
        (Enclosure.sfrac false 12 1)))
    (@Inv.inv Real Real.instInv p19939))
  139987891500527243

noncomputable def p20148 :=
nat_lit
  3502028197540076936989409561542520744864617613442209307954533220255938143425075951697764393276388959481561090672856792353127205435981967767578862330854707292664059040927382656305150625

noncomputable def p20149 :=
nat_lit
  2178277692162336552334210823830993527480916445808945067736080098377285534642208035632331795700607427515318401628905609891325433160271558750439837766290244738452552471416348252603817089600646192711282203342941544175856356174338530270889

noncomputable def p20150 :=
nat_lit
  608089465217626759660921001684341961856453675593242145107309684144869239700708569126041468650040026279691799013693215413418094179226504516312520939809768923082256444364105120049470731433681926496838483968

noncomputable def p20151 :=
@p20147 288230376151711744 457909616401221664253 p4996
  p20148 p18475 p20149 p20127
  p20150 p20125 p18475 p20126

noncomputable def p20152 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  (@Inv.inv Real Real.instInv
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
          (Enclosure.sfrac false 12 1)))))

noncomputable def p20153 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
        (Enclosure.sfrac false 12 1))
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
        (Enclosure.sfrac false 12 1)))
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
      (Enclosure.sfrac false 12 1)))

noncomputable def p20154 :=
@Enclosure.Real.IsNear.of_eq
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
      (Enclosure.sfrac false 12 1)))
  (p20152
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p20153 (Enclosure.sfrac false 1 16)))))

noncomputable def p20155 :=
BSN.cos_two_pi_p_ne_zero_mk
  (@OfScientific.ofScientific Real c2 101903100
    true 5)
  101903100 100000 12
  (Enclosure.sfrac_ofScientific_eq 101903100 5 100000 (Eq.refl true))

noncomputable def p20156 :=
@Enclosure.Real.IsNear.mulLit_tt
  (@Inv.inv Real Real.instInv
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
          (Enclosure.sfrac false 12 1)))))

noncomputable def p20157 :=
@p20156
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p20153 (Enclosure.sfrac false 1 16))))
  1439715749

noncomputable def p20158 :=
@p20157 134217728 15143 8589934592 97233007
  2147483648 4145663807 110729625600000000 139987891500527243
  288230376151711744 457909616401221664253 p4996

noncomputable def p20159 :=
@Enclosure.Real.IsNear.of_eq
  (@Inv.inv Real Real.instInv
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
          (Enclosure.sfrac false 12 1)))))

noncomputable def p20160 :=
@Inv.inv Real Real.instInv
  (@Neg.neg Real Real.instNeg
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
          (Enclosure.sfrac false 12 1)))))

noncomputable def p20161 :=
@p20159 (@Neg.neg Real Real.instNeg p20160) true 1439715749
  134217728 15143 8589934592
  (BSN.inv_eq_neg_inv_neg
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
          (Enclosure.sfrac false 12 1)))))

noncomputable def p20162 :=
@Enclosure.Real.IsNear.inv_image
  (@Neg.neg Real Real.instNeg
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
          (Enclosure.sfrac false 12 1)))))

noncomputable def p20163 :=
@Enclosure.Real.IsNear.neg
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
        (Enclosure.sfrac false 12 1))))
  true

noncomputable def p20164 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
        (Enclosure.sfrac false 12 1))))
  true

noncomputable def p20165 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
      (Enclosure.sfrac false 12 1)))
  (@HDiv.hDiv Real Real Real c4
    (@Nat.cast Real Real.instNatCast 19838575299)
    (@Nat.cast Real Real.instNatCast 4294967296))
  false

noncomputable def p20166 :=
nat_lit 11168125040564547561129505

noncomputable def p20167 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
      (Enclosure.sfrac false 12 1)))
  false p20166

noncomputable def p20168 :=
nat_lit 1106429200258495394559261919

noncomputable def p20169 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
    (Enclosure.sfrac false 12 1))
  884279719003555 140737488355328 1

noncomputable def p20170 :=
@Enclosure.Real.IsNear.subLit_ff_p p19939 (Enclosure.sfrac false 12 1)
  218788059499 17179869184 41 17179869184 12 1 0

noncomputable def p20171 :=
@p20169 500000000000000 12629629291 17179869184 41
  17179869184 p20166 p2602 p20168
  p5018 d141
  (@p20170 1 12629629291 12629629291 17179869184 41
    17179869184 (p20143 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p20172 :=
@p20165 19838575299 4294967296 129 8589934592 true
  1601596017 17179869184 1 3300000000
  (@p20167 p2602 p20168 p5018
    19838575299 4294967296 129 8589934592
    (p20171 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div 19838575299 4294967296)

noncomputable def p20173 :=
nat_lit 914488343870608362981818368

noncomputable def p20174 :=
BSN.cos_reduce2
  (@HDiv.hDiv Real Real Real c4
    (@Nat.cast Real Real.instNatCast 19838575299)
    (@Nat.cast Real Real.instNatCast 4294967296))
  (@HDiv.hDiv Real Real Real c4
    (@Nat.cast Real Real.instNatCast p20173)
    (@Nat.cast Real Real.instNatCast p504))
  226375608064910080 72057594037927936 false

noncomputable def p20175 :=
BSN.sin_reduce_arg_pos_rat_q2 19838575299 4294967296 226375608064910080
  72057594037927936 0 p20173 p504 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p20176 :=
nat_lit
  343232246844270523005809936413307457732603485378310207935710073309653497011076548748594817040075547568659921935092407861603589565037246566793527026362565119064606585654161

noncomputable def p20177 :=
nat_lit
  389314322270963872557037362668694722186798928298473340390229089488416791550399404104081971244852663850234061427260769616290593568184859381559604598610031932808891281

noncomputable def p20178 :=
nat_lit
  2078347738243517910872101308765290409862861009016474619448370250592411405760783980109563384067686430522435087856739503326194707892074138451243490751075179561297593771232145

noncomputable def p20179 :=
BSN.cos_dyadic_bound_f 51982643973963 35184372088832 4 3 17179869184
  6606445313 p20176 p2613 p20177
  p20178 p2616

noncomputable def p20180 :=
@BSN.binarySplit_of_base3 (BSN.cosEvenP 51982643973963) (BSN.cosEvenQ 35184372088832) 0
  3 p20176 p2613 p20177 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20181 :=
p20179 p20177 1601596017 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p20180 (Eq.refl true))

noncomputable def p20182 :=
@BSN.binarySplit_of_base3 (BSN.cosOddP 51982643973963) (BSN.cosOddQ 35184372088832) 0
  3 p20178 p2616 p20177 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20183 :=
@BSN.cos_arg_round false 1601596017 17179869184 p20173 p504
  51982643973963 35184372088832 6606445313 6600000000
  (p20181 (p20182 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p20184 :=
p20174 1601596017 17179869184 0 1000000000000000
  6600000000 3300000000 p20175 BSN.pi_near_15 p20183
  (Eq.refl true) (Eq.refl true)

noncomputable def p20185 :=
@p20163 1601596017 17179869184 1696445057 110729625600000000
  (@p20164 1601596017 17179869184 434289934592
    28346784153600000000 1601596017 17179869184 1696445057
    110729625600000000
    (p20172 (p20184 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p20186 :=
@p20162 1601596017 17179869184 1696445057 110729625600000000
  92141792793 92141823079 8589934592 p20185
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p20187 :=
@Enclosure.Real.IsNear.recentre' p20160 false 184283615872 17179869184
  30286 17179869184 1439715749 134217728 15143 8589934592
  (p20186 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p20188 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p20153 (Enclosure.sfrac false 1 16))))
  true

noncomputable def p20189 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p20153 (Enclosure.sfrac false 1 16)))
  (@HDiv.hDiv Real Real Real c4
    (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 27764205489))
    (@Nat.cast Real Real.instNatCast 17179869184))
  true

noncomputable def p20190 :=
nat_lit 67129729755619423319941843150337845

noncomputable def p20191 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p20153 (Enclosure.sfrac false 1 16)))
  true p20190

noncomputable def p20192 :=
nat_lit 46955886287145499830749746129918193697

noncomputable def p20193 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (p20153 (Enclosure.sfrac false 1 16)) 884279719003555
  140737488355328 1

noncomputable def p20194 :=
@Enclosure.Real.IsNear.subLit_tf
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
        (Enclosure.sfrac false 12 1))
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
        (Enclosure.sfrac false 12 1)))
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
      (Enclosure.sfrac false 12 1)))

noncomputable def p20195 :=
@p20194 (Enclosure.sfrac false 1 16) 57467843033709505863
  295147905179352825856 1740004240087 295147905179352825856 1 16
  0

noncomputable def p20196 :=
@Enclosure.Real.IsNear.subLit_ff_n
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
      (Enclosure.sfrac false 12 1))
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
      (Enclosure.sfrac false 12 1)))
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
    (Enclosure.sfrac false 12 1))
  159507536028085162681

noncomputable def p20197 :=
nat_lit 987290025605775012983621025792

noncomputable def p20198 :=
@p20196 295147905179352825856 1035629603543 295147905179352825856
  12629629291 17179869184 41 17179869184 p20197
  57467843033709505863 295147905179352825856 1740004240087

noncomputable def p20199 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
    (Enclosure.sfrac false 12 1))
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
    (Enclosure.sfrac false 12 1))
  12629629291 17179869184 41

noncomputable def p20200 :=
@p20199 17179869184 12629629291 17179869184 41
  17179869184 159507536028085162681 295147905179352825856 1035629603543
  295147905179352825856
  (@p20170 1 12629629291 12629629291 17179869184 41
    17179869184 (p20143 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p20201 :=
p20200
  (@p20170 1 12629629291 12629629291 17179869184 41
    17179869184 (p20143 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p20202 :=
@p20198 295147905179352825856 (p20201 (Eq.refl true))
  (@p20170 1 12629629291 12629629291 17179869184 41
    17179869184 (p20143 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p20203 :=
@p20193 500000000000000 75914587107419057479 295147905179352825856
  1740004240087 295147905179352825856 p20190 p2630
  p20192 p2632 d141
  (@p20195 1 1214633393718704919664 75914587107419057479
    295147905179352825856 1740004240087 295147905179352825856
    (p20202 (Eq.refl true) (Eq.refl true))
    (Enclosure.Real.IsNear.const false 1 16) (Eq.refl true)
    (Eq.refl true))

noncomputable def p20204 :=
@p20189 27764205489 17179869184 319 8589934592 true
  388932028 8589934592 1 3300000000
  (@p20191 p2630 p20192 p2632
    27764205489 17179869184 319 8589934592
    (p20203 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_true_div 27764205489 17179869184)

noncomputable def p20205 :=
nat_lit
  343833639131896482391541816003830043882531349597724860217546756817264998004209457134644181455963931352679813674044331540057552848205958525814498680739268025032482568636427088641

noncomputable def p20206 :=
nat_lit
  124670585996236207083353100901585081412696353733520056801524190471465041704749358968656367609707850420690228173884243535677628832176622005598839470180083904290209084161

noncomputable def p20207 :=
nat_lit
  3497641594359805708143990877347987029577837069432534489388185419118555229900555662639582032165975141310077179475549566858486029854355725230055998924246386065368905067176744661761

noncomputable def p20208 :=
BSN.cos_dyadic_bound_t 27764205489 17179869184 5 4 8589934592
  3300000000 p20205 p3287 p20206
  p20207 p3290

noncomputable def p20209 :=
@BSN.binarySplit_of_base4 (BSN.cosEvenP 27764205489) (BSN.cosEvenQ 17179869184) 0
  4 p20205 p3287 p20206 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20210 :=
p20208 p20206 388932028 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p20209 (Eq.refl true))

noncomputable def p20211 :=
@BSN.binarySplit_of_base4 (BSN.cosOddP 27764205489) (BSN.cosOddQ 17179869184) 0
  4 p20207 p3290 p20206 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20212 :=
p20204
  (BSN.cos_neg_of_bound 27764205489 17179869184 true 388932028 8589934592
    1 3300000000
    (p20210 (p20211 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p20213 :=
p20158
  (p20161
    (@Enclosure.Real.IsNear.neg p20160 false 1439715749 134217728
      15143 8589934592 (p20187 (Eq.refl true))))
  (@p20188 388932028 8589934592 1061289934592
    28346784153600000000 97233007 2147483648 4145663807
    110729625600000000 (p20212 (Eq.refl true)) (Eq.refl true))

noncomputable def p20214 :=
@p20151 p20127
  (@p20154 false 139987891500527243 288230376151711744
    457909616401221664253 p4996
    (BSN.correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
        (Enclosure.sfrac false 12 1))
      (p20155 (Eq.refl true) (Eq.refl true)
        (p19942 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p20213 (Eq.refl true)))

noncomputable def p20215 :=
nat_lit
  2595993195593447881415862266717092337441390014448327313424955163534025638589652041913611200872631089743247043547529949414801763772946730164172825471339972034576434760345195625

noncomputable def p20216 :=
@Enclosure.Real.IsNear.mulLit_tf
  (Zeta.RiemannSiegel.correctionLinear
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
      (Enclosure.sfrac false 12 1)))
  (@Inv.inv Real Real.instInv p19939) p20215 p18566

noncomputable def p20217 :=
nat_lit
  1613914302310830848376386341988524229718048930068060215223203480051365708474022987250112371573331955215553442098178485205549841149064275611667892691147071216981540162969163089834608528272739790074279161098205671352644417568433

noncomputable def p20218 :=
nat_lit
  106004006587236364632826181999315168302309713288818344979355358072666387468725672695172370463709281865797268475282504826096897723054843254516296929752961714749440000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p20219 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  (@iteratedDeriv Real c11 Real
    Real.normedAddCommGroup
    c8
    (@OfNat.ofNat Nat 3 (instOfNatNat 3)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
      (Enclosure.sfrac false 12 1)))
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 96 1)
      c12))

noncomputable def p20220 :=
@Enclosure.Real.IsNear.of_eq
  (Zeta.RiemannSiegel.correctionLinear
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
      (Enclosure.sfrac false 12 1)))
  (@Neg.neg Real Real.instNeg p20219) true p20215

noncomputable def p20221 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@iteratedDeriv Real c11 Real
    Real.normedAddCommGroup
    c8
    (@OfNat.ofNat Nat 3 (instOfNatNat 3)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
      (Enclosure.sfrac false 12 1)))
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 96 1)
      c12))

noncomputable def p20222 :=
nat_lit
  2184614163673924176753610395161510476985856159378248578745441722406515731308005393751132826000373117705102087262293014642521146520591125903026447191911724939198625

noncomputable def p20223 :=
nat_lit
  1358161512992946043679945913893074218860527255556584980631505530925189698630581067768884272044187026763263394485833689777014351487024825614374914066114339482589939775463376775403612998274232921852646040715308176553

noncomputable def p20224 :=
nat_lit
  94150471052533259659634785165241027284741293791386547144522152728166719509706503905708148550698838855230537770142355947641819223163788925138370560000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p20225 :=
@p20221 p20222 p18574 p20223
  p20224 1188307408585 1125899906842624 1 1125899906842624
  p20215 p18566 p20217

noncomputable def p20226 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p20227 :=
p20226
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p20228 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p20227
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p20229 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p20228
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p20153 (Enclosure.sfrac false 1 16)))))

noncomputable def p20230 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  (Enclosure.sfrac false 3 1)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p20231 :=
p20229
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p20230
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 4 1) Real.pi))
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p20153 (Enclosure.sfrac false 1 16)))))

noncomputable def p20232 :=
@Neg.neg Real Real.instNeg
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
          (Enclosure.sfrac false 12 1)))))

noncomputable def p20233 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20231
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 3 1) p20232)
    (@iteratedDeriv Real c11 Real
      Real.normedAddCommGroup
      c9
      (@OfNat.ofNat Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
        (Enclosure.sfrac false 12 1))))

noncomputable def p20234 :=
@Neg.neg Real Real.instNeg
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 4 1)
      c12)
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
          (Enclosure.sfrac false 12 1)))))

noncomputable def p20235 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20233
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 3 1) p20234)
    (@iteratedDeriv Real c11 Real
      Real.normedAddCommGroup
      c9
      (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
        (Enclosure.sfrac false 12 1))))

noncomputable def p20236 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 8 1)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      c12 Real.pi))
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
        (Enclosure.sfrac false 12 1))))

noncomputable def p20237 :=
@Enclosure.Real.IsNear.of_eq
  (@iteratedDeriv Real c11 Real
    Real.normedAddCommGroup
    c8
    (@OfNat.ofNat Nat 3 (instOfNatNat 3)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
      (Enclosure.sfrac false 12 1)))
  (p20152
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20235
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p20236
        (Zeta.RiemannSiegel.correction
          (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
            (Enclosure.sfrac false 12 1))))))

noncomputable def p20238 :=
@p20156
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20235
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p20236
      (Zeta.RiemannSiegel.correction
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
          (Enclosure.sfrac false 12 1)))))
  12077209737414889

noncomputable def p20239 :=
nat_lit
  180887325066985049358333755582626986008923663008833631314402480509320196843740053911993294612507078603913926375111172720927769972169203568336037625

noncomputable def p20240 :=
nat_lit
  562281861227634540296120444276849286307533137945739884622043243684675055668451325120687158378945904334691555726301076748734973519978391785180885093912252065130929531889878130696788540444991732495557

noncomputable def p20241 :=
nat_lit
  418112082967306884649415655476016994306315472013697785522810658101663248186004046694588913938068048171594782803161453921888842547200000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p20242 :=
@p20238 1125899906842624 30631 1125899906842624 p20239
  p18592 p20240 p20241 p20222
  p18574 p20223 p20224

noncomputable def p20243 :=
@p20159 (@Neg.neg Real Real.instNeg p20160) true
  12077209737414889 1125899906842624 30631 1125899906842624
  (BSN.inv_eq_neg_inv_neg
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
          (Enclosure.sfrac false 12 1)))))

noncomputable def p20244 :=
nat_lit 243497021772966081331200000000

noncomputable def p20245 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
      (Enclosure.sfrac false 12 1)))
  (@HDiv.hDiv Real Real Real c4
    c61
    c42)
  false

noncomputable def p20246 :=
nat_lit 731914241050848609607885374105

noncomputable def p20247 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
      (Enclosure.sfrac false 12 1)))
  false p20246

noncomputable def p20248 :=
nat_lit 1113538940976286550920232159

noncomputable def p20249 :=
@Enclosure.Real.IsNear.subLit_ff_p p19939 (Enclosure.sfrac false 12 1)
  14338494265508499 1125899906842624 41 1125899906842624 12
  1 0

noncomputable def p20250 :=
@p20137
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 101903100 100000)
    (@Inv.inv Real Real.instInv
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)))
  false 182602748745726092979

noncomputable def p20251 :=
@p20250 1125899906842624000 1019031 1125899906842624000
  (BSN.t_div_two_pi_mk
    (@OfScientific.ofScientific Real c2 101903100
      true 5)
    101903100 100000
    (Enclosure.sfrac_ofScientific_eq 101903100 5 100000 (Eq.refl true)))

noncomputable def p20252 :=
@p20140 1 179192535600709 1125899906842624 1
  1125899906842624 182602748745726092979 1125899906842624000 1019031
  1125899906842624000 (Enclosure.Real.IsNear.const false 101903100 100000)
  d239

noncomputable def p20253 :=
@p20136 182602748745726092979 1125899906842624000 1019031
  1125899906842624000 7169247132754229 7169247132754270 562949953421312
  (p20251 (p20252 (Eq.refl true))) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20254 :=
@Enclosure.Real.IsNear.recentre' p19939 false 14338494265508499
  1125899906842624 41 1125899906842624 14338494265508499
  1125899906842624 41 1125899906842624
  (p20253 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p20255 :=
@p20169 500000000000000 827695383397011 1125899906842624 41
  1125899906842624 p20246 p3344 p20248
  p6907 d238
  (@p20249 1 827695383397011 827695383397011 1125899906842624
    41 1125899906842624 (p20254 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p20256 :=
@p20245 5200563471780473 1125899906842624 261 1125899906842624
  true 104962207975993 1125899906842624 1 216268800000000
  (@p20247 p3344 p20248 p6907
    5200563471780473 1125899906842624 261 1125899906842624
    (p20255 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div 5200563471780473 1125899906842624)

noncomputable def p20257 :=
nat_lit 239727630772619595486100629487616

noncomputable def p20258 :=
BSN.cos_reduce2
  (@HDiv.hDiv Real Real Real c4
    c61
    c42)
  (@HDiv.hDiv Real Real Real c4
    (@Nat.cast Real Real.instNatCast p20257)
    (@Nat.cast Real Real.instNatCast p18612))
  226375608064910080 72057594037927936 false

noncomputable def p20259 :=
BSN.sin_reduce_arg_pos_rat_q2 5200563471780473 1125899906842624 226375608064910080
  72057594037927936 0 p20257 p18612
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p20260 :=
nat_lit
  8745261005749338310224295279027253779819726190221372201202678485595340385348803527226269879708596768622405416732906649900771939005216084155705598164052410861524649180380201394667073667078839454977211401374429732313840088557745467472760031121124069115959208155401536116588189840251854937121246489665929095824378452986088632094382474295043323640138750165848695107636734567274739983712256

noncomputable def p20261 :=
nat_lit
  44336954142573223168485214499237733503332123014585106655079150736446033381820891603882271263765742895305395236004292265831138028476370031352409679737963225936188132945960157430899451512837307416184744892739859341386934443429326553346228350445350804085944391308158541923438984759505047687667690002524697638555168086940277012996526875660947263717569413362436216492681854976

noncomputable def p20262 :=
nat_lit
  134422972003786888613557147363610741804843436370860800337180057782860514617497039591180395121973203357112551037088731856761045434051070608763487721765983380055052108764648119377389514523048735085840598604307694954503785909717708603159997363642877128653394201288351426624497158594470729123151923318816892823348467104305960223072272760456221433412360059609327942417934676926766037635956736

noncomputable def p20263 :=
BSN.cos_dyadic_bound_f 3406734532129286144 2305843009213693952 6 5
  1125899906842624 432960000000001 p20260 p18616
  p20261 p20262 p18619

noncomputable def p20264 :=
@BSN.binarySplit_of_base5 (BSN.cosEvenP 3406734532129286144) (BSN.cosEvenQ 2305843009213693952)
  0 5 p20260 p18616 p20261
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p20265 :=
p20263 p20261 104962207975993 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p20264 (Eq.refl true))

noncomputable def p20266 :=
@BSN.binarySplit_of_base5 (BSN.cosOddP 3406734532129286144) (BSN.cosOddQ 2305843009213693952)
  0 5 p20262 p18619 p20261
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p20267 :=
@BSN.cos_arg_round false 104962207975993 1125899906842624 p20257
  p18612 3406734532129286144 2305843009213693952 432960000000001
  432537600000000
  (p20265 (p20266 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p20268 :=
p20258 104962207975993 1125899906842624 0 1000000000000000
  432537600000000 216268800000000 p20259 BSN.pi_near_15 p20267
  (Eq.refl true) (Eq.refl true)

noncomputable def p20269 :=
@p20163 104962207975993 1125899906842624 3431561989
  14513553486643200000000
  (@p20164 104962207975993 1125899906842624 57572056706842624
    p20244 104962207975993 1125899906842624 3431561989
    14513553486643200000000
    (p20256 (p20268 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p20270 :=
@p20162 104962207975993 1125899906842624 3431561989
  14513553486643200000000 6038604868692129 6038604868722760 562949953421312
  p20269 (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p20271 :=
@Enclosure.Real.IsNear.recentre' p20160 false 12077209737414889
  1125899906842624 30631 1125899906842624 12077209737414889
  1125899906842624 30631 1125899906842624
  (p20270 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p20272 :=
nat_lit
  24145629437317135486399732346026403774006951467056749056410771523089695603535040545130392209969808472935930548601066595756309010880156280868560037625

noncomputable def p20273 :=
@Enclosure.Real.IsNear.subLit_tt_n p20235
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p20236
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
        (Enclosure.sfrac false 12 1))))
  p20272 p18592

noncomputable def p20274 :=
nat_lit
  561509923241144829977265182490821544535867672752330440213435469024039706084433816260489083580790154013795876893620681260823100864693829181747324199244212031800530729693681261925295881244991732495557

noncomputable def p20275 :=
nat_lit 119306365035627979159253750531699623228969723692091264320953719367241112311782684227546875

noncomputable def p20276 :=
nat_lit 994646472819573284310764496293641680200912301594695434880927953786318994025066751066112

noncomputable def p20277 :=
nat_lit
  1734549033147070043309769098949201907113166646829044897293300177185848224569467005810761831920657864347726313037595599595573

noncomputable def p20278 :=
nat_lit
  939500221456865495564556141752460089714907208836693869821498609964679168000000000000000000000000000000000000000000000000000000000000

noncomputable def p20279 :=
nat_lit
  179918939855644262116350349130627758119772018389811015516672293371927805306884773921997253229326665448296597210286135588420794311391635704750357938365888866126326840145648290118977131024525842938600388561054068351990575782338494464000

noncomputable def p20280 :=
@p20273 p20274 p20241 p20275
  p20276 p20277 p20278 p20279
  p20239 p18592 p20240 p20241

noncomputable def p20281 :=
@Enclosure.Real.IsNear.subLit_tf p20233
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 3 1) p20234)
    (@iteratedDeriv Real c11 Real
      Real.normedAddCommGroup
      c9
      (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
        (Enclosure.sfrac false 12 1))))

noncomputable def p20282 :=
nat_lit
  22099055505950852395651832025498426383050063081680032460944962281308336355948465617120369830113823653853134443030491627134932977090633899895676069625

noncomputable def p20283 :=
nat_lit
  559066201945763657837951238002109315147294463730931299766839227755224221257500502210707096427411333249175514222280162813661858980616371934562988601771912646201870436392443857015767390582038772495557

noncomputable def p20284 :=
nat_lit
  12915697312794647719467416513882029795085577224656635613677542453537156128879733726000093094416909260382745252141884625

noncomputable def p20285 :=
nat_lit
  5981885884298876211805913860372355126576799518983330018659295505750469634136196288826931292384624430224565793171189804388452295535527900349090069601673751592113

noncomputable def p20286 :=
nat_lit
  1023479548131863275080398600728202591233031898932413741247824456804094803805051725949002513576529756160000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p20287 :=
nat_lit
  30444359702560470877840262191611703793704579206175261441145118907899464264223577916852388249228604279587635507481432888187496362849828831817041581468685443225636421722374904073107402223014137212997563071098933249640165307971803088945461296910048698071879688126464000

noncomputable def p20288 :=
@p20281 p20282 p18592 p20283
  p20241 p20284 p18754 p20285
  p20286 p20287 p20272 p18592

noncomputable def p20289 :=
@Enclosure.Real.IsNear.subLit_tf p20231
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 3 1) p20232)
    (@iteratedDeriv Real c11 Real
      Real.normedAddCommGroup
      c9
      (@OfNat.ofNat Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
        (Enclosure.sfrac false 12 1))))

noncomputable def p20290 :=
nat_lit 362725789588163841711857740888796373397566622203490164428282146528744454209229984475988048118729688375

noncomputable def p20291 :=
nat_lit 17498005798264095394980017816940970922825355447145699491406164851279623993595007385788105416184430592

noncomputable def p20292 :=
nat_lit
  1558434274169479483531214719749220146907499909167438521998030677996303176591968740901755502602050425423694600467320260587579439

noncomputable def p20293 :=
nat_lit
  17095486251586415824091264780046966378453180183658827787015949205702357709805834783948800000000000000000000000000000000000000000000000000

noncomputable def p20294 :=
nat_lit
  17957459135753617764647549635820391996315342356926772968784776056750706493554606417703106437643878406182490851606344643676815454849421232742849701625

noncomputable def p20295 :=
nat_lit
  559028086609881931904685669156382763408774344534244461526142635125261974511612956845575000287969659264896953215813586493549692134649027565005193462254701967078418441044697041015767390582038772495557

noncomputable def p20296 :=
nat_lit
  386689401379288097514687374612958361177210399911576492307918069870940119437794846807471114731228328995016608130492422229356120503879793989918855464167596228972260622150324274732524299310631539426541904948855048553037955845781373891083864761171968000

noncomputable def p20297 :=
@p20289 p20290 p20291 p20292
  p20293 p20294 p18592 p20295
  p20241 p20296 p20282 p18592

noncomputable def p20298 :=
@Enclosure.Real.IsNear.subLit_tt_n
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p20228
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p20153 (Enclosure.sfrac false 1 16)))))

noncomputable def p20299 :=
@p20298
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p20230
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 4 1) Real.pi))
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p20153 (Enclosure.sfrac false 1 16)))))

noncomputable def p20300 :=
nat_lit 450981359767523290260576050279880032344871119582823769110289223212936644930857063298799346088332248375

noncomputable def p20301 :=
nat_lit
  457094786105310624446965129261358623344958226785593218575351306536083489075887519468549459644522577325769321214840260587579439

noncomputable def p20302 :=
nat_lit 15830066554937281990856856030413618198460670889191680343125

noncomputable def p20303 :=
nat_lit 161827293319617579295916379593140072327999307188041532107811393179875358429

noncomputable def p20304 :=
nat_lit 2511955939162489390662583306231111440033634058240000000000000000000000000000000000000

noncomputable def p20305 :=
nat_lit
  1138433341646683635827329311975416682277698671392554700046692366575662868880294754094456865822491360105986201884076630953578735600035905843348651809693499392000

noncomputable def p20306 :=
@p20299 p20300 p20291 p20301
  p20293 p20302 p18881 p20303
  p20304 p20305 p20290 p20291

noncomputable def p20307 :=
nat_lit 12830819925759096619945294726562398427546261369395655015435661311346565557453115835583625

noncomputable def p20308 :=
@Enclosure.Real.IsNear.mulLit_ft p20228
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p20153 (Enclosure.sfrac false 1 16))))
  p20307

noncomputable def p20309 :=
nat_lit 1358197606676983308288510978714389662767873615091536069735707567315699334733541307394133759635245064966271

noncomputable def p20310 :=
nat_lit
  113078212145816597093331040047546785012958969400039613319782796882727665664000000000000000000000000000000000000000000

noncomputable def p20311 :=
@p20308 p18666 p20309 p20310
  35148288447423 35184372088832 4145663807 7256776743321600000000
  p20300 p20291 p20301 p20293

noncomputable def p20312 :=
@Enclosure.Real.IsNear.mulLit_ff p20227
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p20313 :=
nat_lit 54807030635694022970994296475916821841343919911316192903025

noncomputable def p20314 :=
nat_lit 633685112960943207343495493183354228258926958627416907876385026831

noncomputable def p20315 :=
nat_lit 233840261972944466912589573234605283144949206876160000000000000000000000000000

noncomputable def p20316 :=
nat_lit 234109014426386458552144609945

noncomputable def p20317 :=
nat_lit 221740647539565606844281491

noncomputable def p20318 :=
nat_lit 483570327845851669882470400000000000000

noncomputable def p20319 :=
@p20312 p20313 p18672 p20314
  p20315 p20316 p2316 p20317
  p20318 p20307 p18666 p20309

noncomputable def p20320 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p20321 :=
@p20320
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p20322 :=
@p20321 p20316 p2316 p20317
  p20318 p20316 p2316 p20317
  p20318 p20313 p18672 p20314

noncomputable def p20323 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
        (Enclosure.sfrac false 12 1)))
    (Enclosure.sfrac false 1 1))
  884279719003555

noncomputable def p20324 :=
@p20323 140737488355328 1 500000000000000 264745429975699
  562949953421312 41 562949953421312 p20316 p2316
  p20317 p20318

noncomputable def p20325 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
      (Enclosure.sfrac false 12 1)))
  (Enclosure.sfrac false 1 1) 827695383397011 562949953421312

noncomputable def p20326 :=
@p20325 41 562949953421312 1 1 0 1
  264745429975699 264745429975699 562949953421312 41 562949953421312

noncomputable def p20327 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 2 1)
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
    (Enclosure.sfrac false 12 1))
  2 1 0 1

noncomputable def p20328 :=
@p20327 827695383397011 1125899906842624 41 1125899906842624
  827695383397011 562949953421312 41 562949953421312
  (Enclosure.Real.IsNear.const false 2 1)
  (@p20249 1 827695383397011 827695383397011 1125899906842624
    41 1125899906842624 (p20254 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p20329 :=
@p20322 p20315
  (p20324 d238
    (p20326 (p20328 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (p20324 d238
    (p20326 (p20328 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))

noncomputable def p20330 :=
@p20319 p20310 (p20329 (Eq.refl true))
  (p20324 d238
    (p20326 (p20328 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p20331 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p20153 (Enclosure.sfrac false 1 16))))
  true

noncomputable def p20332 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p20153 (Enclosure.sfrac false 1 16)))
  (@HDiv.hDiv Real Real Real c4
    (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 1819554976357037))
    c42)
  true

noncomputable def p20333 :=
nat_lit 288319994740907487127402866834269786453495845

noncomputable def p20334 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p20153 (Enclosure.sfrac false 1 16)))
  true p20333

noncomputable def p20335 :=
nat_lit 3080101667910384836939411552215064319714257

noncomputable def p20336 :=
nat_lit 326050669878303945355989213079

noncomputable def p20337 :=
nat_lit 246822507364039607762445262743

noncomputable def p20338 :=
@p20194 (Enclosure.sfrac false 1 16) p20337
  p14431 114032917619104167 p14431 1 16 0

noncomputable def p20339 :=
nat_lit 5216810718052863125695827409264

noncomputable def p20340 :=
nat_lit 685079647696725032558043734121

noncomputable def p20341 :=
@Enclosure.Real.IsNear.subLit_ff_n
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
      (Enclosure.sfrac false 12 1))
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
      (Enclosure.sfrac false 12 1)))
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
    (Enclosure.sfrac false 12 1))
  p20340

noncomputable def p20342 :=
nat_lit 277897438047835070605130502103711679231557632

noncomputable def p20343 :=
@p20341 p14431 67871021438556583 p14431
  827695383397011 1125899906842624 41 1125899906842624 p20342
  p20337 p14431 114032917619104167

noncomputable def p20344 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
    (Enclosure.sfrac false 12 1))
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
    (Enclosure.sfrac false 12 1))
  827695383397011 1125899906842624 41

noncomputable def p20345 :=
@p20344 1125899906842624 827695383397011 1125899906842624 41
  1125899906842624 p20340 p14431 67871021438556583
  p14431
  (@p20249 1 827695383397011 827695383397011 1125899906842624
    41 1125899906842624 (p20254 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p20346 :=
p20345
  (@p20249 1 827695383397011 827695383397011 1125899906842624
    41 1125899906842624 (p20254 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p20347 :=
@p20343 p14431 (p20346 (Eq.refl true))
  (@p20249 1 827695383397011 827695383397011 1125899906842624
    41 1125899906842624 (p20254 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p20348 :=
@p20193 500000000000000 p20336 p14431
  114032917619104167 p14431 p20333 p18695
  p20335 p18697 d238
  (@p20338 1 p20339 p20336 p14431
    114032917619104167 p14431
    (p20347 (Eq.refl true) (Eq.refl true))
    (Enclosure.Real.IsNear.const false 1 16) (Eq.refl true)
    (Eq.refl true))

noncomputable def p20349 :=
@p20332 1819554976357037 1125899906842624 319 562949953421312
  true 562372615158768 562949953421312 1 216268800000000
  (@p20334 p18695 p20335 p18697
    1819554976357037 1125899906842624 319 562949953421312
    (p20348 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_true_div 1819554976357037 1125899906842624)

noncomputable def p20350 :=
nat_lit
  135121455698204895810455557557143883063917391095433276513862299339794064687465149680109820393490127734044697662023839145911983109243659999585005793480511438941556076748792777494751360978214098222564978199438036615019493856674446770692221585290780136592961

noncomputable def p20351 :=
nat_lit
  14435868308219124561887831006668873180290569487352518374598975105844411915467663641342335204876929991483346300615763635503158361795295459129028661045277270914721947164362772616929588464113019476606155574468899196091150375361946694341997842290241

noncomputable def p20352 :=
nat_lit
  1098743123836689672217613482601708333577587115189579379080474363071770424571159306025053967082292233409442165116933517733215324069112300098792750238371446702274812376726186244466082257416776146611769878701469147145732914106109532219562551581982762457781825

noncomputable def p20353 :=
BSN.sin_dyadic_bound_f 1819554976357037 1125899906842624 5 4
  562949953421312 216268800000000 p20350 p18713
  p20351 p20352 p18716

noncomputable def p20354 :=
@BSN.binarySplit_of_base4 (BSN.sinEvenP 1819554976357037) (BSN.sinEvenQ 1125899906842624)
  0 4 p20350 p18713 p20351
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p20355 :=
p20353 p20351 562372615158768 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p20354 (Eq.refl true))

noncomputable def p20356 :=
@BSN.binarySplit_of_base4 (BSN.sinOddP 1819554976357037) (BSN.sinOddQ 1125899906842624) 0
  4 p20352 p18716 p20351 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20357 :=
p20349
  (BSN.sin_neg_of_bound 1819554976357037 1125899906842624 false 562372615158768
    562949953421312 1 216268800000000
    (p20355 (p20356 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p20358 :=
p20311 p20330
  (@p20331 562372615158768 562949953421312 69552697153421312
    p18691 35148288447423 35184372088832 4145663807
    7256776743321600000000 (p20357 (Eq.refl true))
    (Eq.refl true))

noncomputable def p20359 :=
nat_lit 621053560479492663900544159169046238630063425

noncomputable def p20360 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p20230
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 4 1) Real.pi))
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p20153 (Enclosure.sfrac false 1 16))))
  p20359

noncomputable def p20361 :=
nat_lit 17988551671345597726533321496570393527932493347069391

noncomputable def p20362 :=
nat_lit 1038459371706965525706099265844019200000000000000000000000000000

noncomputable def p20363 :=
@p20360 p18725 p20361 p20362
  25489052091925 562949953421312 4145663807 7256776743321600000000
  p20302 p18881 p20303 p20304

noncomputable def p20364 :=
nat_lit 702327043279159375656433829835

noncomputable def p20365 :=
nat_lit 665221942618696820532844473

noncomputable def p20366 :=
@Enclosure.Real.IsNear.mulLit_ff p20230
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 4 1) Real.pi)
  p20364 p2316 p20365 p20318

noncomputable def p20367 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 3 1)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p20368 :=
@p20367 3 1 0 1 p20316
  p2316 p20317 p20318 p20364
  p2316 p20365

noncomputable def p20369 :=
@p20368 p20318 (Enclosure.Real.IsNear.const false 3 1)
  (p20324 d238
    (p20326 (p20328 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p20370 :=
@p20366 884279719003555 70368744177664 1 250000000000000
  p20359 p18725 p20361 p20362
  p20369 d240 (Eq.refl true)

noncomputable def p20371 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p20153 (Enclosure.sfrac false 1 16)))
  (@HDiv.hDiv Real Real Real c4
    (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 1819554976357037))
    c42)
  true

noncomputable def p20372 :=
@p20371 1819554976357037 1125899906842624 319 562949953421312
  true 25489052091925 562949953421312 1 216268800000000
  (@p20334 p18695 p20335 p18697
    1819554976357037 1125899906842624 319 562949953421312
    (p20348 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_true_div 1819554976357037 1125899906842624)

noncomputable def p20373 :=
nat_lit
  7439288734500717268400185287932845529088546577211629389742066008211142307322509718816420338862800750650597375687310447041434492703264410019980537525991527874581028634787502385022757659195816161131550930891450479730198033983236820484968071215000412757776986377878924321602486882056805667722416581709928866083454643289681

noncomputable def p20374 :=
nat_lit
  158235396426134646349990462842571726669915321771500206350780791887270282861280482559613486723517402951467869503098120133045401195520409203091402177882104827957469809848170942400973382280190786103004771503369613420699953061065844903436203933096138690368087047784276260414391244627890034538479995443927006801

noncomputable def p20375 :=
nat_lit
  114255970900129351650792339512271260828709104596112584882123393947942236353067888363990522148032967344645187688021668162800342005649445837311288383847182457489942660561309587730772345557160428994464560623618729704965919111427610533307738290218678502311522195990614387148894669080005295199180568480886565550209301885959761

noncomputable def p20376 :=
BSN.cos_dyadic_bound_t 1819554976357037 1125899906842624 6 5
  562949953421312 216268800000000 p20373 p18739
  p20374 p20375 p18742

noncomputable def p20377 :=
@BSN.binarySplit_of_base5 (BSN.cosEvenP 1819554976357037) (BSN.cosEvenQ 1125899906842624)
  0 5 p20373 p18739 p20374
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p20378 :=
p20376 p20374 25489052091925 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p20377 (Eq.refl true))

noncomputable def p20379 :=
@BSN.binarySplit_of_base5 (BSN.cosOddP 1819554976357037) (BSN.cosOddQ 1125899906842624) 0
  5 p20375 p18742 p20374 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20380 :=
p20372
  (BSN.cos_neg_of_bound 1819554976357037 1125899906842624 true 25489052091925
    562949953421312 1 216268800000000
    (p20378 (p20379 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p20381 :=
p20363 p20370
  (@p20188 25489052091925 562949953421312 69552697153421312
    p18691 25489052091925 562949953421312 4145663807
    7256776743321600000000 (p20380 (Eq.refl true))
    (Eq.refl true))

noncomputable def p20382 :=
nat_lit 1486911931103491238841276491325

noncomputable def p20383 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 3 1) p20232)
  (@iteratedDeriv Real c11 Real
    Real.normedAddCommGroup
    c8
    (@OfNat.ofNat Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
      (Enclosure.sfrac false 12 1)))
  p20382

noncomputable def p20384 :=
nat_lit 92728518147579222019402926729595363

noncomputable def p20385 :=
nat_lit 20778412524626438940262400000000000000000000000

noncomputable def p20386 :=
nat_lit
  12077015968542761273032774256516557198120842583206362704101441660483738787354291923241854969452759655818969014798666605

noncomputable def p20387 :=
nat_lit
  2521728396569246669585858566409191283525103313309788586748690777871726193375821479130513040312634601011624191379636224

noncomputable def p20388 :=
nat_lit
  2867072364616318837063800259524058913871573368090398868148618876123209665507595186199248147358624905807545647922460233218511856450903588204182960811303

noncomputable def p20389 :=
nat_lit
  40244853399821874957401401618394091011428787117060800167850454160667894237300721947076297237850872459821056000000000000000000000000000000000000000000000000000

noncomputable def p20390 :=
@p20383 p2316 p20384 p20385
  p20386 p20387 p20388 p20389
  p20294 p18592 p20295 p20241

noncomputable def p20391 :=
nat_lit 495637310367830412947092163775

noncomputable def p20392 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 3 1) p20232
  3 1 0 1 p20391 p2316

noncomputable def p20393 :=
nat_lit 62335237573879316820787200000000000000000000000

noncomputable def p20394 :=
@Enclosure.Real.IsNear.neg
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
          (Enclosure.sfrac false 12 1)))))

noncomputable def p20395 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
        (Enclosure.sfrac false 12 1))))
  884279719003555

noncomputable def p20396 :=
@p20395 140737488355328 1 500000000000000 560498335217205
  562949953421312 3431561989 14513553486643200000000 p20391
  p2316 p20384 p20393

noncomputable def p20397 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
        (Enclosure.sfrac false 12 1))))
  true

noncomputable def p20398 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
      (Enclosure.sfrac false 12 1)))
  (@HDiv.hDiv Real Real Real c4
    c61
    c42)
  false

noncomputable def p20399 :=
@p20398 5200563471780473 1125899906842624 261 1125899906842624
  true 1120996670434410 1125899906842624 1 216268800000000
  (@p20247 p3344 p20248 p6907
    5200563471780473 1125899906842624 261 1125899906842624
    (p20255 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div 5200563471780473 1125899906842624)

noncomputable def p20400 :=
BSN.sin_reduce2
  (@HDiv.hDiv Real Real Real c4
    c61
    c42)
  (@HDiv.hDiv Real Real Real c4
    (@Nat.cast Real Real.instNatCast p20257)
    (@Nat.cast Real Real.instNatCast p18612))
  226375608064910080 72057594037927936 false

noncomputable def p20401 :=
nat_lit
  9034023206807530836472507561506960762815460022632041202188764577761841241345231980415013738121530218656208310892970921651082353412855208308769273910909669105551840261525718952083121406601914818204441278026770522918025129862489423635749633717970468615877712374103888698220060636797122559415097467060854194176

noncomputable def p20402 :=
nat_lit
  329164267172761075560075440079103797658324052737211508295620215601359195570115005557248021006335865410326623973943160345299534922963277190812285252347493048855359682222842389712501539504949437838511114174649195856932262640315074354330180941079217923482676196768765997225414219225599627277218349056

noncomputable def p20403 :=
nat_lit
  73491195708736695552345511649632808240293481040724059956017641205706696782424725671622229496676575941711562648367142883035725926499664209188160564292109003579614489722719571433551620516771726213559060940216334829933812289534194927836154105292505384937308847710688027625358304008327800841315507753864994488320

noncomputable def p20404 :=
BSN.sin_dyadic_bound_f 3406734532129286144 2305843009213693952 5 4
  1125899906842624 432960000000001 p20401 p18769
  p20402 p20403 p18772

noncomputable def p20405 :=
@BSN.binarySplit_of_base4 (BSN.sinEvenP 3406734532129286144) (BSN.sinEvenQ 2305843009213693952)
  0 4 p20401 p18769 p20402
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p20406 :=
p20404 p20402 1120996670434410 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p20405 (Eq.refl true))

noncomputable def p20407 :=
@BSN.binarySplit_of_base4 (BSN.sinOddP 3406734532129286144) (BSN.sinOddQ 2305843009213693952)
  0 4 p20403 p18772 p20402
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p20408 :=
@BSN.sin_arg_round false 1120996670434410 1125899906842624 p20257
  p18612 3406734532129286144 2305843009213693952 432960000000001
  432537600000000
  (p20406 (p20407 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p20409 :=
p20400 1120996670434410 1125899906842624 0 1000000000000000
  432537600000000 216268800000000 p20259 BSN.pi_near_15 p20408
  (Eq.refl true) (Eq.refl true)

noncomputable def p20410 :=
p20396 d238
  (@p20397 1120996670434410 1125899906842624 57572056706842624
    p20244 560498335217205 562949953421312 3431561989
    14513553486643200000000
    (p20399 (p20409 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p20411 :=
@Neg.neg Real Real.instNeg
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p20227
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p20153 (Enclosure.sfrac false 1 16)))))

noncomputable def p20412 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20411
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 4 1) Real.pi)
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p20153 (Enclosure.sfrac false 1 16)))))

noncomputable def p20413 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20412
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) p20232)
    (@iteratedDeriv Real c11 Real
      Real.normedAddCommGroup
      c9
      (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
        (Enclosure.sfrac false 12 1))))

noncomputable def p20414 :=
@Enclosure.Real.IsNear.of_eq
  (@iteratedDeriv Real c11 Real
    Real.normedAddCommGroup
    c8
    (@OfNat.ofNat Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
      (Enclosure.sfrac false 12 1)))
  (p20152
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20413
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p20234
        (Zeta.RiemannSiegel.correction
          (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
            (Enclosure.sfrac false 12 1))))))

noncomputable def p20415 :=
@p20156
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20413
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p20234
      (Zeta.RiemannSiegel.correction
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
          (Enclosure.sfrac false 12 1)))))
  12077209737414889

noncomputable def p20416 :=
nat_lit 999983955824537232642140031802520675431599203889624554426902987775951665884273208803908241849995369445

noncomputable def p20417 :=
nat_lit
  1186773926876898228446986177910184868063496595038078355928037299522145667160068748702259899328431744570995726013378681064805919215343307

noncomputable def p20418 :=
nat_lit
  178723051468585025591379718516523005306900926912042849216579539376094728441394119165314334720000000000000000000000000000000000000000000000000000

noncomputable def p20419 :=
@p20415 1125899906842624 30631 1125899906842624 p20416
  p8045 p20417 p20418 p20386
  p20387 p20388 p20389

noncomputable def p20420 :=
nat_lit 3003537495048652733711070108211113123642553333411312851033478242480057323712354192843979248663637910555

noncomputable def p20421 :=
@Enclosure.Real.IsNear.subLit_ff_n p20413
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p20234
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
        (Enclosure.sfrac false 12 1))))
  p20420 p8045

noncomputable def p20422 :=
nat_lit
  1181122448298550087571251219224059442529249934573688918300994394016635258825920835189153471914012075880586399131339037884217846255343307

noncomputable def p20423 :=
nat_lit 25265772446460505447651036674598570799937440871419336118113850487575068125

noncomputable def p20424 :=
nat_lit 13834024361589515791968826179970819052485350354355139499456680850577136462352656248301658190296863

noncomputable def p20425 :=
nat_lit 437488882549510102516299179639881518536669765057365349410799616000000000000000000000000000000000000000000000

noncomputable def p20426 :=
nat_lit
  14134549737392489197607890205186311613870414399099172235964527963973941798333119954930445071776447155099830994233147392913746637617857890785750391561791557683979192424265154560

noncomputable def p20427 :=
@p20421 p20422 p20418 p20423
  p18825 p20424 p20425 p20426
  p20416 p8045 p20417 p20418

noncomputable def p20428 :=
@Enclosure.Real.IsNear.subLit_ff_p p20412
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) p20232)
    (@iteratedDeriv Real c11 Real
      Real.normedAddCommGroup
      c9
      (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
        (Enclosure.sfrac false 12 1))))

noncomputable def p20429 :=
nat_lit 45757148663213966004498217640059693018528262269432867044229640434534652485

noncomputable def p20430 :=
nat_lit 3533694129556768659166595001485837031654967793751237916243212402585239552

noncomputable def p20431 :=
nat_lit 20861409468129125399857715651306613636497110003118302202777408252401287782804448223261867

noncomputable def p20432 :=
nat_lit 1696926574737493730972311969512267708263446361434629234078253056000000000000000000000000000000000000

noncomputable def p20433 :=
nat_lit 25998500988779101560080312339927774786795136897070206405938047216076837422655376616584026181959233969125

noncomputable def p20434 :=
nat_lit
  1178925290912022366870711349912501353456819856468116211621868448932428109556230738439355991454901746075302620341134662844217846255343307

noncomputable def p20435 :=
nat_lit
  10613582814157066278349440679448399273454311581258557548669994473967984495285159210389202920786418802302776234355579544900413247227628305125749433009903291049546752573424271360

noncomputable def p20436 :=
@p20428 p20429 p20430 p20431
  p20432 p20433 p8045 p20434
  p20418 p20435 p20420 p8045

noncomputable def p20437 :=
@Enclosure.Real.IsNear.subLit_ft p20411
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 4 1) Real.pi)
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p20153 (Enclosure.sfrac false 1 16)))))

noncomputable def p20438 :=
nat_lit 1396979258876934298783041176186711323137404772268913667194976214910573125

noncomputable def p20439 :=
nat_lit 2890832877361373732697194663233709152122004543776901471847973180352371739441482741087289

noncomputable def p20440 :=
nat_lit 565642191579164576990770656504089236087815453811543078026084352000000000000000000000000000000000000

noncomputable def p20441 :=
nat_lit 31080918631743108879567588765

noncomputable def p20442 :=
nat_lit 111937467425370842977554088361477369

noncomputable def p20443 :=
nat_lit 113289212827452165210122587688042530900147227462818434597545021322487870102998948474328146213370593280

noncomputable def p20444 :=
@p20437 p20438 p20430 p20439
  p20440 p20441 p2333 p20442
  p18760 p20443 p20429 p20430

noncomputable def p20445 :=
@Enclosure.Real.IsNear.neg
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p20227
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p20153 (Enclosure.sfrac false 1 16)))))

noncomputable def p20446 :=
@Enclosure.Real.IsNear.mulLit_ft p20227
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p20153 (Enclosure.sfrac false 1 16))))
  p20313

noncomputable def p20447 :=
@p20446 p18672 p20314 p20315
  25489052091925 562949953421312 4145663807 7256776743321600000000
  p20438 p20430 p20439 p20440

noncomputable def p20448 :=
p20447 (p20329 (Eq.refl true))
  (@p20188 25489052091925 562949953421312 69552697153421312
    p18691 25489052091925 562949953421312 4145663807
    7256776743321600000000 (p20380 (Eq.refl true))
    (Eq.refl true))

noncomputable def p20449 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 4 1) Real.pi)
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p20153 (Enclosure.sfrac false 1 16))))
  884279719003555

noncomputable def p20450 :=
@p20449 70368744177664 1 250000000000000 35148288447423
  35184372088832 4145663807 7256776743321600000000 p20441
  p2333 p20442 p18760

noncomputable def p20451 :=
p20450 d240
  (@p20331 562372615158768 562949953421312 69552697153421312
    p18691 35148288447423 35184372088832 4145663807
    7256776743321600000000 (p20357 (Eq.refl true))
    (Eq.refl true))

noncomputable def p20452 :=
@p20436 p20422 p20418
  (@p20444 p20431 p20432
    (@p20445 true p20438 p20430 p20439
      p20440 (p20448 (Eq.refl true)))
    (p20451 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p20453 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1) p20232)
  (@iteratedDeriv Real c11 Real
    Real.normedAddCommGroup
    c8
    (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
      (Enclosure.sfrac false 12 1)))
  p20391

noncomputable def p20454 :=
nat_lit 39614081257132168796771975168

noncomputable def p20455 :=
nat_lit 31167618786939658410393600000000000000000000000

noncomputable def p20456 :=
nat_lit 52454689033569066121860955102271713605567124371831091363800882903666535515

noncomputable def p20457 :=
nat_lit 56539106072908298546665520023773392506479484700019806659891398441363832832

noncomputable def p20458 :=
nat_lit 6043889096087437439152293311434189516272490981700802805158656900488751964365408054508553

noncomputable def p20459 :=
nat_lit 11468508562705877631403273214751710079527675889119798215594465453670400000000000000000000000000000

noncomputable def p20460 :=
@p20453 p20454 p20384 p20455
  p20456 p20457 p20458 p20459
  p20433 p8045 p20434 p20418

noncomputable def p20461 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 2 1) p20232
  2 1 0 1 p20391 p2316

noncomputable def p20462 :=
@Neg.neg Real Real.instNeg
  (p20226
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p20153 (Enclosure.sfrac false 1 16)))))

noncomputable def p20463 :=
@Enclosure.Real.IsNear.of_eq
  (@iteratedDeriv Real c11 Real
    Real.normedAddCommGroup
    c8
    (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
      (Enclosure.sfrac false 12 1)))
  (p20152
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20462
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p20232
        (Zeta.RiemannSiegel.correction
          (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
            (Enclosure.sfrac false 12 1))))))

noncomputable def p20464 :=
@p20156
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20462
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p20232
      (Zeta.RiemannSiegel.correction
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
          (Enclosure.sfrac false 12 1)))))
  12077209737414889

noncomputable def p20465 :=
nat_lit 4343278801482247333036672838938829256840340359180586729635

noncomputable def p20466 :=
nat_lit 50216813883093446110686315385661331328818843555712276103168

noncomputable def p20467 :=
nat_lit 2491015444787308509984183948795445612451001730408620874762990833231503557

noncomputable def p20468 :=
nat_lit 50930409057707304893562009050497030668969937257627648000000000000000000000000000000

noncomputable def p20469 :=
@p20464 1125899906842624 30631 1125899906842624 p20465
  p20466 p20467 p20468 p20456
  p20457 p20458 p20459

noncomputable def p20470 :=
nat_lit 8228531167200543606187950212770721975421735

noncomputable def p20471 :=
@Enclosure.Real.IsNear.subLit_ff_n p20462
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p20232
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
        (Enclosure.sfrac false 12 1))))
  p20470 p1061

noncomputable def p20472 :=
nat_lit 627596792036040453106298352108097338759843921301

noncomputable def p20473 :=
nat_lit 292430159072681492038837553261675806720000000000000000000000

noncomputable def p20474 :=
nat_lit 152575318395125770142430353135126848965083261649975371251875

noncomputable def p20475 :=
nat_lit 2381711529476179363434717742440655580292667523979368436977389194831503557

noncomputable def p20476 :=
nat_lit 12107294234754383342084235990452153967470512328972367276139844694313501323368267287889446352474603520

noncomputable def p20477 :=
@p20471 p20472 p20473 p20474
  p20466 p20475 p20468 p20476
  p20465 p20466 p20467 p20468

noncomputable def p20478 :=
@Enclosure.Real.IsNear.neg
  (p20226
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p20153 (Enclosure.sfrac false 1 16)))))

noncomputable def p20479 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p20480 :=
@p20479
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p20153 (Enclosure.sfrac false 1 16))))
  p20316

noncomputable def p20481 :=
@p20480 p2316 p20317 p20318
  35148288447423 35184372088832 4145663807 7256776743321600000000
  p20470 p1061 p20472 p20473

noncomputable def p20482 :=
p20481
  (p20324 d238
    (p20326 (p20328 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (@p20331 562372615158768 562949953421312 69552697153421312
    p18691 35148288447423 35184372088832 4145663807
    7256776743321600000000 (p20357 (Eq.refl true))
    (Eq.refl true))

noncomputable def p20483 :=
@Enclosure.Real.IsNear.mulLit_ff p20232
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
      (Enclosure.sfrac false 12 1)))
  p20391 p2316 p20384

noncomputable def p20484 :=
nat_lit 307836628122071956407091671325

noncomputable def p20485 :=
nat_lit 12026494642639853001143303

noncomputable def p20486 :=
nat_lit 1634080851856701962866843975680000000

noncomputable def p20487 :=
@p20156
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p20153 (Enclosure.sfrac false 1 16))))
  12077209737414889

noncomputable def p20488 :=
@p20487 1125899906842624 30631 1125899906842624 25489052091925
  562949953421312 4145663807 7256776743321600000000 p20484
  p2704 p20485 p20486

noncomputable def p20489 :=
p20488
  (p20243
    (@Enclosure.Real.IsNear.neg p20160 false 12077209737414889
      1125899906842624 30631 1125899906842624
      (p20271 (Eq.refl true))))
  (@p20188 25489052091925 562949953421312 69552697153421312
    p18691 25489052091925 562949953421312 4145663807
    7256776743321600000000 (p20380 (Eq.refl true))
    (Eq.refl true))

noncomputable def p20490 :=
@p20483 p20393 p20484 p2704
  p20485 p20486 p20474 p20466
  p20475 p20468
  (@p20394 true p20391 p2316 p20384
    p20393 (p20410 (Eq.refl true)))
  (@p20154 false p20484 p2704 p20485
    p20486
    (BSN.correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
        (Enclosure.sfrac false 12 1))
      (p20155 (Eq.refl true) (Eq.refl true)
        (p19942 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p20489 (Eq.refl true)))

noncomputable def p20491 :=
p20469
  (p20243
    (@Enclosure.Real.IsNear.neg p20160 false 12077209737414889
      1125899906842624 30631 1125899906842624
      (p20271 (Eq.refl true))))
  (p20477
    (@p20478 true p20470 p1061 p20472
      p20473 (p20482 (Eq.refl true)))
    (p20490 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p20492 :=
p20460
  (@p20461 p20384 p20393 p20391
    p20454 p20384 p20455
    (Enclosure.Real.IsNear.const false 2 1)
    (@p20394 true p20391 p2316 p20384
      p20393 (p20410 (Eq.refl true)))
    (Eq.refl true))
  (@p20463 false p20456 p20457 p20458
    p20459
    (BSN.deriv_correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
        (Enclosure.sfrac false 12 1))
      (p20155 (Eq.refl true) (Eq.refl true)
        (p19942 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p20491 (Eq.refl true)))

noncomputable def p20493 :=
nat_lit 82075263754647862854361540331149681168933825

noncomputable def p20494 :=
nat_lit 2499656355429568385587361051100944250540896408237426304700021

noncomputable def p20495 :=
@Enclosure.Real.IsNear.mulLit_ff p20234
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
      (Enclosure.sfrac false 12 1)))
  p20493 p2325 p20494

noncomputable def p20496 :=
nat_lit 267727806768202049596103716975411200000000000000000000000000000000000000

noncomputable def p20497 :=
@Enclosure.Real.IsNear.neg
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 4 1)
      c12)
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
          (Enclosure.sfrac false 12 1)))))

noncomputable def p20498 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 4 1)
    c12)
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
        (Enclosure.sfrac false 12 1))))
  p1068

noncomputable def p20499 :=
@p20498 p1070 p1071 p1072
  104962207975993 1125899906842624 3431561989 14513553486643200000000
  p20493 p2325 p20494 p20496

noncomputable def p20500 :=
p20499 d242
  (@p20164 104962207975993 1125899906842624 57572056706842624
    p20244 104962207975993 1125899906842624 3431561989
    14513553486643200000000
    (p20256 (p20268 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p20501 :=
@p20495 p20496 p20484 p2704
  p20485 p20486 p20423 p18825
  p20424 p20425
  (@p20497 true p20493 p2325 p20494
    p20496 (p20500 (Eq.refl true)))
  (@p20154 false p20484 p2704 p20485
    p20486
    (BSN.correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
        (Enclosure.sfrac false 12 1))
      (p20155 (Eq.refl true) (Eq.refl true)
        (p19942 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p20489 (Eq.refl true)))

noncomputable def p20502 :=
p20419
  (p20243
    (@Enclosure.Real.IsNear.neg p20160 false 12077209737414889
      1125899906842624 30631 1125899906842624
      (p20271 (Eq.refl true))))
  (p20427
    (p20452 (p20492 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true))
    (p20501 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p20503 :=
p20390
  (@p20392 p20384 p20393 p20382
    p2316 p20384 p20385
    (Enclosure.Real.IsNear.const false 3 1)
    (@p20394 true p20391 p2316 p20384
      p20393 (p20410 (Eq.refl true)))
    (Eq.refl true))
  (@p20414 false p20386 p20387 p20388
    p20389
    (BSN.iteratedDeriv_two_correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
        (Enclosure.sfrac false 12 1))
      (p20155 (Eq.refl true) (Eq.refl true)
        (p19942 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p20502 (Eq.refl true)))

noncomputable def p20504 :=
@p20297 p20283 p20241
  (@p20306 p20292 p20293
    (p20358 (Eq.refl true)) (p20381 (Eq.refl true))
    (Eq.refl true) (Eq.refl true))
  (p20503 (Eq.refl true)) (Eq.refl true) (Eq.refl true)

noncomputable def p20505 :=
nat_lit 246225791263943588563084620993449043506801475

noncomputable def p20506 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 3 1) p20234)
  (@iteratedDeriv Real c11 Real
    Real.normedAddCommGroup
    c8
    (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
      (Enclosure.sfrac false 12 1)))
  p20505

noncomputable def p20507 :=
nat_lit 89242602256067349865367905658470400000000000000000000000000000000000000

noncomputable def p20508 :=
@p20506 p2325 p20494 p20507
  p20456 p20457 p20458 p20459
  p20284 p18754 p20285 p20286

noncomputable def p20509 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 3 1) p20234
  3 1 0 1 p20493 p2325

noncomputable def p20510 :=
p20508
  (@p20509 p20494 p20496 p20505
    p2325 p20494 p20507
    (Enclosure.Real.IsNear.const false 3 1)
    (@p20497 true p20493 p2325 p20494
      p20496 (p20500 (Eq.refl true)))
    (Eq.refl true))
  (@p20463 false p20456 p20457 p20458
    p20459
    (BSN.deriv_correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
        (Enclosure.sfrac false 12 1))
      (p20155 (Eq.refl true) (Eq.refl true)
        (p19942 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p20491 (Eq.refl true)))

noncomputable def p20511 :=
nat_lit 387563902851473851595744230369840785373864342791732842544375

noncomputable def p20512 :=
nat_lit 1569275433846670190958947355801916604025588861116008628224

noncomputable def p20513 :=
nat_lit 67710173881996857391680614691893739747958928232125290042983657560413218070373603448307

noncomputable def p20514 :=
@Enclosure.Real.IsNear.mulLit_tf p20236
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
      (Enclosure.sfrac false 12 1)))
  p20511 p20512 p20513

noncomputable def p20515 :=
nat_lit 1149882174299235255735435473433431140152115200000000000000000000000000000000000000000000000000000

noncomputable def p20516 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 8 1)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      c12 Real.pi))
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
        (Enclosure.sfrac false 12 1))))

noncomputable def p20517 :=
@p20516 p1059 p1061 p1062
  p1063 560498335217205 562949953421312 3431561989
  14513553486643200000000 p20511 p20512 p20513

noncomputable def p20518 :=
@p20517 p20515 d243
  (@p20397 1120996670434410 1125899906842624 57572056706842624
    p20244 560498335217205 562949953421312 3431561989
    14513553486643200000000
    (p20399 (p20409 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p20519 :=
@p20514 p20515 p20484 p2704
  p20485 p20486 p20275 p20276
  p20277 p20278 (p20518 (Eq.refl true))
  (@p20154 false p20484 p2704 p20485
    p20486
    (BSN.correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
        (Enclosure.sfrac false 12 1))
      (p20155 (Eq.refl true) (Eq.refl true)
        (p19942 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p20489 (Eq.refl true)))

noncomputable def p20520 :=
p20242
  (p20243
    (@Enclosure.Real.IsNear.neg p20160 false 12077209737414889
      1125899906842624 30631 1125899906842624
      (p20271 (Eq.refl true))))
  (p20280
    (@p20288 p20274 p20241 p20504
      (p20510 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true))
    (p20519 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p20521 :=
@p20225 p20218
  (@p20237 false p20222 p18574 p20223
    p20224
    (BSN.iteratedDeriv_three_correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
        (Enclosure.sfrac false 12 1))
      (p20155 (Eq.refl true) (Eq.refl true)
        (p19942 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p20520 (Eq.refl true)))

noncomputable def p20522 :=
@p20216 p20217 p20218 1349012857 17179869184
  1 17179869184 p20148 p18475 p20149
  p20127
  (@p20220 p18566 p20217 p20218
    (BSN.correctionLinear_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p19939
        (Enclosure.sfrac false 12 1)))
    (@Enclosure.Real.IsNear.neg p20219 false p20215 p18566
      p20217 p20218
      (p20521 d244 (Eq.refl true))))

noncomputable def p20523 :=
@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv p19939) false
  1349012857 17179869184 1 17179869184 1349012857
  17179869184

noncomputable def p20524 :=
@Enclosure.Real.IsNear.inv_image p19939 218788059499 17179869184 41
  17179869184 674506428 674506429 8589934592
  (p20143 (Eq.refl true)) (Eq.refl true) (Eq.refl true)

noncomputable def p20525 :=
p20214
  (p20522
    (@p20523 1 17179869184
      (p20524 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (Eq.refl true))
    (Eq.refl true))

noncomputable def p20526 :=
@p20128 p19934
  (@p20130 8589934592
    (@p2563 1 0 1
      (BSN.neg_one_pow_even_mk 12 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1))
    p20146 (Eq.refl true))
  (p20525 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p20527 :=
@p19941 p19931 p19933 p19934
  (BSN.hardyZApproximantRS_eq
    (@OfScientific.ofScientific Real c2 101903100
      true 5)
    12
    (p19942 (Eq.refl true) (Eq.refl true)
      (Eq.refl true)))
  (p20123 p20526 (Eq.refl true) (Eq.refl true))

theorem d257 : p19932 p19933 p19934 :=
@p19935 p19931 p19933 p19934
  (@Eq.refl Real
    (hardyZApproximantRS
      (@OfScientific.ofScientific Real c2 101903100
        true 5)))
  p20527

noncomputable def p20528 :=
@p2043 1 54400000000 157330477519 137438953472 1
  54400000000 78665238759 68719476736 2 68719476736 BSN.pi_near_15

noncomputable def p20529 :=
BSN.logfrac_isNear p507 p596 1 p497
  p593 157330477519 137438953472 54400000000
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p20530 :=
BSN.log_dyadic_bound p598 p599 20 19 p2046
  137438953472 54400000000 p2047 p2048 157330477519
  p507

noncomputable def p20531 :=
p20530 p596 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p20532 :=
p20528 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)
  (BSN.isNear_log_sfrac p497 p593 157330477519 137438953472
    1 54400000000 false
    (p20529
      (p20531 p2056 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))))

noncomputable def p20533 :=
BSN.logfrac_isNear p520 p596 1 p499
  p593 157330477519 137438953472 54400000000
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p20534 :=
BSN.log_dyadic_bound p617 p618 20 19 p2059
  137438953472 54400000000 p2060 p2061 157330477519
  p520

noncomputable def p20535 :=
p20534 p596 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p20536 :=
p20532
  (BSN.isNear_log_sfrac p499 p593 157330477519 137438953472
    1 54400000000 false
    (p20533
      (p20535 p2069 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))))
  (Eq.refl true) (Eq.refl true)

theorem d258 : Enclosure.Real.IsNear (Real.log Real.pi) false 78665238759 68719476736 1
  34359738368 :=
p2042
  (p20536 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

theorem d259 : Enclosure.Real.IsNear Real.pi false 226375608064910080 72057594037927936 1
  1000000000000000 :=
BSN.pi_near_15

theorem d260 : p2306 500000000000000 :=
@p501 1 1000000000000000 884279719003555 140737488355328
  1 500000000000000 (Enclosure.Real.IsNear.const false 2 1)
  d259 (Eq.refl true)

noncomputable def p20537 :=
@p2308 1 17179869184 2734261103 17179869184 1
  17179869184
  (@p2309 1367130551 1367130552 8589934592 d260
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))

theorem d261 : p2307 1 17179869184 :=
p20537 (Eq.refl true)

theorem d262 : Enclosure.Real.IsNear Real.pi false p2138 p2102 1
  p2139 :=
d102

noncomputable def p20538 :=
nat_lit 4701637434417376175498040524537150595537054745004197

noncomputable def p20539 :=
nat_lit 748288838313422294120286634350736906063837462003712

noncomputable def p20540 :=
Enclosure.Real.IsNear
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  false p20538 p20539 1

noncomputable def p20541 :=
nat_lit 50000000000000000000000000000000000000000000000000

noncomputable def p20542 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 2 1) Real.pi 2 1
  0 1 p2138 p2102

theorem d263 : p20540 p20541 :=
@p20542 1 p2139 p20538 p20539
  1 p20541 (Enclosure.Real.IsNear.const false 2 1) d262
  (Eq.refl true)

noncomputable def p20543 :=
Enclosure.Real.IsNear
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi))
  false 2867080569611329 18014398509481984

noncomputable def p20544 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi))
  false 2867080569611329 18014398509481984

noncomputable def p20545 :=
@Enclosure.Real.IsNear.inv_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  p20538 p20539 1 p20541

noncomputable def p20546 :=
@p20544 1 18014398509481984 2867080569611329 18014398509481984
  1 18014398509481984
  (@p20545 1433540284805664 1433540284805665 9007199254740992
    d263 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))

theorem d264 : p20543 1 18014398509481984 :=
p20546 (Eq.refl true)

noncomputable def p20547 :=
Enclosure.Real.IsNear
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 4 1) Real.pi)
  false p20538 p2930 1

noncomputable def p20548 :=
nat_lit 25000000000000000000000000000000000000000000000000

noncomputable def p20549 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 4 1) Real.pi 4 1
  0 1 p2138 p2102

theorem d265 : p20547 p20548 :=
@p20549 1 p2139 p20538 p2930
  1 p20548 (Enclosure.Real.IsNear.const false 4 1) d262
  (Eq.refl true)

noncomputable def p20550 :=
nat_lit 22105394564714807257736884719499096650845483332447810269516804581135915889100039191225953062529547614809

noncomputable def p20551 :=
nat_lit 417589290650377635882687645766355774726812799091764503857183322408181176654048939000413

noncomputable def p20552 :=
Enclosure.Real.IsNear c12 false
  p20550 p8045 p20551

noncomputable def p20553 :=
nat_lit
  6646139978924579364519035301401722880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p20554 :=
@Enclosure.Real.IsNear.mulLit_ff Real.pi Real.pi p2138 p2102 1
  p2139 p2138 p2102 1 p2139
  p20550

theorem d266 : p20552 p20553 :=
@p20554 p8045 p20551 p20553 d262
  d262 (Eq.refl true)

noncomputable def p20555 :=
nat_lit 559936185544451052639360570142111069530411374308662383724997275240947967795040236345219373317901778944

noncomputable def p20556 :=
Enclosure.Real.IsNear
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 4 1)
    c12)
  false p20550 p20555

noncomputable def p20557 :=
nat_lit
  1661534994731144841129758825350430720000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p20558 :=
@p2321 p20550 p8045 p20551
  p20553 p20550 p20555 p20551
  p20557 (Enclosure.Real.IsNear.const false 4 1) d266
  (Eq.refl true)

theorem d267 : p20556 p20551 p20557 :=
p20558

noncomputable def p20559 :=
nat_lit
  103931550588029538378366461842947243015660045946545572208368375324223393219452690028515025292633050266996218646796411168437656550155835735595042230044353373

noncomputable def p20560 :=
nat_lit
  523142446997656712469753551493125581454272032392013901160201314287547242054593516501802209746311642665899898626345723419458089834363728689138839025920005516356297821165666651

noncomputable def p20561 :=
nat_lit
  220855883097298041197912187592864814478435487109452369765200775161577472000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p20562 :=
nat_lit
  1766847064778384329583297500742918515827483896875618958121606201292619776000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p20563 :=
@p2324 0 1 p20559 p5674
  p20560 p20562 p20559 p13788
  p20560 p20561 (Enclosure.Real.IsNear.const false 8 1)

noncomputable def p20564 :=
@Enclosure.Real.IsNear.mulLit_ff c12
  Real.pi p20550 p8045 p20551

noncomputable def p20565 :=
@p20564 p20553 p2138 p2102 1
  p2139 p20559 p5674 p20560
  p20562 d266 d262

theorem d268 : p2323 p20559 p13788 p20560
  p20561 :=
p20563 (p20565 (Eq.refl true)) (Eq.refl true)

noncomputable def p20566 :=
Enclosure.Real.IsNear
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 96 1)
      c12))
  false 19012918537349

noncomputable def p20567 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 96 1)
      c12))
  false 19012918537349

noncomputable def p20568 :=
nat_lit 66316183694144421773210654158497289952536449997343430808550413743407747667300117573677859187588642844427

noncomputable def p20569 :=
nat_lit 1252767871951132907648062937299067324180438397275293511571549967224543529962146817001239

noncomputable def p20570 :=
@Enclosure.Real.IsNear.inv_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 96 1)
    c12)
  p20568 p2848 p20569

noncomputable def p20571 :=
nat_lit
  207691874341393105141219853168803840000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p20572 :=
@p2337 p20550 p8045 p20551
  p20553 p20568 p2848 p20569
  p20571 (Enclosure.Real.IsNear.const false 96 1) d266
  (Eq.refl true)

noncomputable def p20573 :=
@p20570 p20571 9506459268674 9506459268675
  9007199254740992 p20572 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

theorem d269 : p20566 18014398509481984 1 18014398509481984 :=
@p20567 18014398509481984 1 18014398509481984 19012918537349
  18014398509481984 1 18014398509481984 p20573
  (Eq.refl true)

noncomputable def p20574 :=
nat_lit
  257773601349797440700550136102152864842649666530721397622929550447874524286809082477429212672391742583682455472462801407845502823593044540644459322875212664885166853214607835305049371599813967350016476899970906165719215511183877314915495114061766455799479013053510532969163385021545338622796638384021521558433

noncomputable def p20575 :=
nat_lit
  359538626972463181545861038157804946723595395788461314546860162315465351611001926265416954644815072042240227759742786715317579537628833244985694861278948248755535786849730970552604439202492188238906165904170011537676301364684925762947826221081654474326701021369172596479894491876959432609670712659248448274432

noncomputable def p20576 :=
Enclosure.Real.IsNear
  (hardyZApproximantRS
    (@OfScientific.ofScientific Real c2 102026300
      true 5))
  false p20574 p20575

noncomputable def p20577 :=
nat_lit
  623430766445402290308938313878728277465323813009293253995406482808098608763409455415702928701982624018077555040535521057116120677410095984468277060320420586820544569402410682374221439524432235766356421272998357811960099560889910762668002632101081917035963515145597506621557505914030549665792699013433571

noncomputable def p20578 :=
nat_lit
  179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416622492847430639474124377767893424865485276302219601246094119453082952085005768838150682342462881473913110540827237163350510684586298239947245938479716304835356329624224137216

noncomputable def p20579 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZApproximantRS
    (@OfScientific.ofScientific Real c2 102026300
      true 5))
  (hardyZApproximantRS
    (@OfScientific.ofScientific Real c2 102026300
      true 5))
  false p20574

noncomputable def p20580 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
  (Zeta.RiemannSiegel.mainSumOfPhase
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 102026300
        true 5))
    (@OfScientific.ofScientific Real c2 102026300
      true 5)
    12)

noncomputable def p20581 :=
@HPow.hPow Real Real Real (@instHPow Real Real Real.instPow)
  (@HDiv.hDiv Real Real Real c4
    (@OfScientific.ofScientific Real c2 102026300
      true 5)
    c7)

noncomputable def p20582 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  c22
  (p20581
    (@Neg.neg Real Real.instNeg
      (@HDiv.hDiv Real Real Real c4
        c37
        c20)))

noncomputable def p20583 :=
Real.sqrt
  (@HDiv.hDiv Real Real Real c4
    (@OfScientific.ofScientific Real c2 102026300
      true 5)
    c7)

noncomputable def p20584 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p20582
  (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
        (Enclosure.sfrac false 12 1)))
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Zeta.RiemannSiegel.correctionLinear
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
          (Enclosure.sfrac false 12 1)))
      (@Inv.inv Real Real.instInv p20583)))

noncomputable def p20585 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZApproximantRS
    (@OfScientific.ofScientific Real c2 102026300
      true 5))
  (p20580 p20584) false p20574

noncomputable def p20586 :=
@BSN.floor_sqrt_eq_dec
  (@OfScientific.ofScientific Real c2 102026300
    true 5)
  102026300 100000 12
  (Enclosure.sfrac_ofScientific_eq 102026300 5 100000 (Eq.refl true))

noncomputable def p20587 :=
nat_lit
  1031094405399189762802200544408611459370598666122885590491718201791498097147236329909716850689566970334729821889851205631382011294372178162577837291500850659540667412858431341220197486399255869400065907599883624662876862044735509259661980456247065823197916052214042131876653540086181354491186553536086086233733

noncomputable def p20588 :=
nat_lit
  1438154507889852726183444152631219786894381583153845258187440649261861406444007705061667818579260288168960911038971146861270318150515332979942779445115792995022143147398923882210417756809968752955624663616680046150705205458739703051791304884326617897306804085476690385919577967507837730438682850636993793097728

noncomputable def p20589 :=
nat_lit
  4987446131563218322471506511029826219722590504074346031963251862464788870107275643325623429615860992144620440324284168456928965419280767875746216482563364694564356555219285458993771516195457886130851370183986862495680796487119286101344021056808655336287708121164780052972460047312244397326341592107468567

noncomputable def p20590 :=
@Enclosure.Real.IsNear.recentre' (p20580 p20584) false p20587
  p20588 p20589 p20588 p20574
  p20575 p20577 p20578

noncomputable def p20591 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (Zeta.RiemannSiegel.mainSumOfPhase
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 102026300
        true 5))
    (@OfScientific.ofScientific Real c2 102026300
      true 5)
    12)

noncomputable def p20592 :=
nat_lit
  198276257019563684623338211112539979974291015404416897074181014125847676338234662615804420375956381834722599821184082478638331319538843561267931810419362296765849715131370729152873440374591572574176227492335702038668671570818756810092040362736404545280041429503892787335266844055344216834957768502095960363387

noncomputable def p20593 :=
nat_lit
  405177243155617516646068881792859492545395376203543082395940020948573745125627426519016964116042894169474119842587893786834211590594036988713007141024055229338783728780536444515507082305943289705289928868908169272965593459378471353459076379634234808045644986844747161722285411004626482053020562708776727

noncomputable def p20594 :=
nat_lit
  17714067001112343424533794620273527515070216059756066913246312942169651752374443734981202025327220743957867032051263369971827079168124536242228728885621489355628787680959569953608659754984835031237320853544232085331980591028970804960613512296689226426377470318450957393505384242371095756258515870689771584858076187983872

noncomputable def p20595 :=
@p20591 p20584 14685784485 17179869184 218955
  68719476736 p20592 p20588 p20593
  p20588 p20594 p20587

noncomputable def p20596 :=
@Enclosure.Real.IsNear.of_eq
  (Zeta.RiemannSiegel.mainSumOfPhase
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 102026300
        true 5))
    (@OfScientific.ofScientific Real c2 102026300
      true 5)
    12)

noncomputable def p20597 :=
@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 102026300
        true 5))
    (@OfScientific.ofScientific Real c2 102026300
      true 5)
    12)

noncomputable def p20598 :=
p20597
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 102026300
        true 5))
    (@OfScientific.ofScientific Real c2 102026300
      true 5)
    12)

noncomputable def p20599 :=
@p20596 p20598 false 14685784485 17179869184
  218955 68719476736
  (BSN.main_sum_of_phase_eq
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 102026300
        true 5))
    (@OfScientific.ofScientific Real c2 102026300
      true 5)
    12)

noncomputable def p20600 :=
@Enclosure.Real.IsNear.addLit_ff
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 102026300
        true 5))
    (@OfScientific.ofScientific Real c2 102026300
      true 5)
    12)

noncomputable def p20601 :=
@p20600
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 102026300
        true 5))
    (@OfScientific.ofScientific Real c2 102026300
      true 5)
    12)

noncomputable def p20602 :=
@p20601 58743137940 137438953472 218955 137438953472
  58743137940 137438953472 218955 137438953472 16147190804269875855360
  14685784485 17179869184

noncomputable def p20603 :=
BSN.mainSumRS_step
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real c2 102026300
      true 5))
  (@OfScientific.ofScientific Real c2 102026300
    true 5)
  Real.sin BSN.quadSignNeg

noncomputable def p20604 :=
p20603 11 12 102026300 100000 285
  137438953472 68719476736 2305843009213693952 false 286699561799107
  3341

noncomputable def p20605 :=
p20604 341522969406 43 39675208392 8 false
  98418130823 205316 true 215435603346 7244019458077122842 1

noncomputable def p20606 :=
p20605 false 137438206926 true false 58743137940 218955
  BSN.abs_quadSignNeg (BSN.cos_quad_nat1 285 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 137438206926 137438953472)
  (Enclosure.sfrac_ofScientific_eq 102026300 5 100000 (Eq.refl true))
  (Eq.refl true)

noncomputable def p20607 :=
BSN.mainSumRS_step2
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real c2 102026300
      true 5))
  (@OfScientific.ofScientific Real c2 102026300
    true 5)
  Real.sin Real.sin

noncomputable def p20608 :=
p20607 BSN.quadSignPos BSN.quadSignNeg 9 10 11 102026300
  100000 167 229 137438953472 68719476736

noncomputable def p20609 :=
p20608 2305843009213693952 false 286699561799107 3341
  316464885454 43 43462013224 8 329564216814 43
  41439403656

noncomputable def p20610 :=
p20609 8 false 92700835820 176132 true 124454882364
  true 104124590826 7244019458077122842 1 false

noncomputable def p20611 :=
p20610 108130297364 false false 94445890303 true false
  98418130823 205316 BSN.abs_quadSignPos
  (BSN.cos_quad_nat3 167 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 108130297364 137438953472)

noncomputable def p20612 :=
BSN.mainSumRS_step2
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real c2 102026300
      true 5))
  (@OfScientific.ofScientific Real c2 102026300
    true 5)
  Real.cos Real.sin

noncomputable def p20613 :=
p20612 BSN.quadSignNeg BSN.quadSignPos 7 8 9 102026300
  100000 22 99 137438953472 68719476736

noncomputable def p20614 :=
p20613 2305843009213693952 false 286699561799107 3341
  285796269294 43 48592008000 16 301984246446 43
  45812984488

noncomputable def p20615 :=
p20614 8 false 108526698367 143675 true 138248027605
  true 30819708665 7244019458077122842 1 false

noncomputable def p20616 :=
p20615 73576488316 true false 30562063100 false false
  92700835820 176132 BSN.abs_quadSignNeg
  (BSN.cos_quad_nat2 22 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 73576488316 137438953472)

noncomputable def p20617 :=
BSN.mainSumRS_step2
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real c2 102026300
      true 5))
  (@OfScientific.ofScientific Real c2 102026300
    true 5)
  Real.cos Real.cos

noncomputable def p20618 :=
p20617 BSN.quadSignPos BSN.quadSignPos 5 6 7 102026300
  100000 164 64 137438953472 68719476736

noncomputable def p20619 :=
p20618 2305843009213693952 false 286699561799107 3341
  246257546308 43 56109217800 8 267443854420 43
  51947041624

noncomputable def p20620 :=
p20619 8 false 4161931797 106536 false 46367893602
  false 19621947563 7244019458077122842 1 false

noncomputable def p20621 :=
p20620 129691272392 false false 136040633432 false false
  108526698367 143675 BSN.abs_quadSignPos
  (BSN.cos_quad_nat0 164 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 129691272392 137438953472)

noncomputable def p20622 :=
BSN.mainSumRS_step2
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real c2 102026300
      true 5))
  (@OfScientific.ofScientific Real c2 102026300
    true 5)
  Real.sin Real.cos

noncomputable def p20623 :=
p20622 BSN.quadSignPos BSN.quadSignNeg 3 4 5 102026300
  100000 427 282 137438953472 68719476736

noncomputable def p20624 :=
p20623 2305843009213693952 false 286699561799107 3341
  190530846192 42 68719476728 8 221199462352 42
  61464568544

noncomputable def p20625 :=
p20624 16 true 16381036679 62754 false 123555473424
  false 137348618665 7244019458077122842 1 false

noncomputable def p20626 :=
p20625 107572807935 false false 74334581550 true false
  4161931797 106536 BSN.abs_quadSignPos
  (BSN.cos_quad_nat3 427 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 107572807935 137438953472)

noncomputable def p20627 :=
p20622 BSN.quadSignNeg BSN.quadSignNeg 1 2 3 102026300
  100000 877 614 137438953472 68719476736

noncomputable def p20628 :=
p20627 2305843009213693952 false 286699561799107 3341
  95265423088 42 97184016000 16 150992123216 42
  79350416784

noncomputable def p20629 :=
p20628 16 false 137438031760 3385 false 169470373221
  false 92282781156 7244019458077122842 1 false

noncomputable def p20630 :=
p20629 129674601963 true false 107604138004 true true
  16381036679 62754 BSN.abs_quadSignNeg
  (BSN.cos_quad_nat1 877 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 129674601963 137438953472)

noncomputable def p20631 :=
@Enclosure.Real.IsNear.recentre'
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 102026300
        true 5))
    (@OfScientific.ofScientific Real c2 102026300
      true 5)
    1)

noncomputable def p20632 :=
@Enclosure.Real.IsNear.of_eq
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 102026300
        true 5))
    (@OfScientific.ofScientific Real c2 102026300
      true 5)
    1)

noncomputable def p20633 :=
@p20632
  (Real.cos
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 102026300
        true 5)))
  false 8589876985

noncomputable def p20634 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 102026300
        true 5)))
  false 17179753970

noncomputable def p20635 :=
@Enclosure.Real.IsNear.cos_image
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real c2 102026300
      true 5))
  (@HDiv.hDiv Real Real Real c4
    (@Nat.cast Real Real.instNatCast 4479680653111)
    (@Nat.cast Real Real.instNatCast 2147483648))
  false 4479680653111

noncomputable def p20636 :=
nat_lit 381463158918198867548089355943806882552511361911998186323001

noncomputable def p20637 :=
nat_lit 182867029934901184964322327707989916969223225820053504000

noncomputable def p20638 :=
@Enclosure.Real.IsNear.recentre'
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real c2 102026300
      true 5))
  false p20636 p20637

noncomputable def p20639 :=
nat_lit 35651584000000000000000000

noncomputable def p20640 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 102026300 400000)
      (Real.log (Enclosure.sfrac false 41637473566760000 160000000000)))
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 1 4)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 1 2) Real.pi)
        (Real.arctan
          (@HDiv.hDiv Real Real Real c4
            (@Nat.cast Real Real.instNatCast 100000)
            (@Nat.cast Real Real.instNatCast 204052600))))))

noncomputable def p20641 :=
nat_lit 530642691996016040263149630820640000000000000000

noncomputable def p20642 :=
nat_lit 3248370993256720584062732507888247769920000000000000

noncomputable def p20643 :=
@Enclosure.Real.IsNear.of_eq
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real c2 102026300
      true 5))
  (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (p20640 (Enclosure.sfrac false 102026300 200000))
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 102026300 200000) (Real.log Real.pi)))
    (Enclosure.sfrac true p20641 p20642))
  false

noncomputable def p20644 :=
BSN.riemannSiegelThetaApproximant_two_zero_mk
  (@OfScientific.ofScientific Real c2 102026300
    true 5)
  102026300 100000 41637473566760000 160000000000

noncomputable def p20645 :=
p20644 204052600 400000 200000 p20641
  p20642
  (Enclosure.sfrac_ofScientific_eq 102026300 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20646 :=
@Enclosure.Real.IsNear.addLit_ft_p
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (p20640 (Enclosure.sfrac false 102026300 200000))
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 102026300 200000) (Real.log Real.pi)))
  (Enclosure.sfrac true p20641 p20642) 37578287906902706835121
  18014398509481984000

noncomputable def p20647 :=
nat_lit 122068210853823637615388593902018202416803635811839419623360320000000000000

noncomputable def p20648 :=
@p20646 866407062541942891 p20639 p20641
  p20642 0 1 p20647 p20636
  p20637 866407062541942891 p20639

noncomputable def p20649 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (p20640 (Enclosure.sfrac false 102026300 200000))
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 102026300 200000) (Real.log Real.pi))
  9619605205618134552509 3602879701896396800 642959239507 68000000000000000000

noncomputable def p20650 :=
nat_lit 1032944112638844278468610298898022400

noncomputable def p20651 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 102026300 400000)
      (Real.log (Enclosure.sfrac false 41637473566760000 160000000000)))
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 1 4)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 1 2) Real.pi)
        (Real.arctan
          (@HDiv.hDiv Real Real Real c4
            (@Nat.cast Real Real.instNatCast 100000)
            (@Nat.cast Real Real.instNatCast 204052600))))))

noncomputable def p20652 :=
@p20651 (Enclosure.sfrac false 102026300 200000)
  57287738161330481483441 18014398509481984000 642959239507 68000000000000000000
  102026300 200000 0

noncomputable def p20653 :=
nat_lit 9619605205618134552509000000

noncomputable def p20654 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 102026300 400000)
    (Real.log (Enclosure.sfrac false 41637473566760000 160000000000)))
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 1 4)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 1 2) Real.pi)
      (Real.arctan
        (@HDiv.hDiv Real Real Real c4
          (@Nat.cast Real Real.instNatCast 100000)
          (@Nat.cast Real Real.instNatCast 204052600)))))
  57294810192005142115441

noncomputable def p20655 :=
nat_lit 129000518118133250035187796172097978368

noncomputable def p20656 :=
@p20654 18014398509481984000 637959231007 68000000000000000000
  884003834332579 2251799813685248 10000017 136000000000000000
  p20655 57287738161330481483441 18014398509481984000 642959239507

noncomputable def p20657 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 102026300 400000)
  (Real.log (Enclosure.sfrac false 41637473566760000 160000000000)) 102026300
  400000 0 1 56156902869167207 4503599627370496

noncomputable def p20658 :=
nat_lit 30872583842268380265044770816

noncomputable def p20659 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv Real Real Real c4
      (@Nat.cast Real Real.instNatCast 41637473566760000)
      (@Nat.cast Real Real.instNatCast 160000000000)))
  false p20658 p2333

noncomputable def p20660 :=
nat_lit 27200000000000000000000000

noncomputable def p20661 :=
BSN.log_rat_reduce_isNear 41637473566760000 160000000000 17 83274947133520000
  41943040000000000 47130238949 68719476736 24973259072661432
  36028797018963968 27200000000 1000000000000000

noncomputable def p20662 :=
nat_lit
  1061736274368224272742551731808859732553445908644149414583920457802701446455083374723591074457550626302668041886760379771647000757499035985791154218749425498730828215922187674761492669507747100967342493450010144051472900024856869182422132345191138937142400579895542176995528288212237865189376000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p20663 :=
nat_lit
  41294757532240965767146360093878710652362814701661519027591271393982601576851810878794049368052063389402311043192874356893043815593426246516919495479082918192865605699001128458500662899004578229526376387060106711686486348045634141334530608318195774012494064132583680198066609477081844259225600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p20664 :=
nat_lit
  1185497945951673867717031650391512992210013578269782262252882793123465484916177422289590728266828437464348604481271888794373601902327184948731696741855394758727907921218649666999646223192212537997355745866120856694461690838413504522512297055663720437158784272844442807641112051712000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p20665 :=
BSN.log_dyadic_bound 20665953566760000 62608993566760000 12 11
  p20662 68719476736 27200000000 p20663 p20664
  47130238949 83274947133520000

noncomputable def p20666 :=
p20665 41943040000000000 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p20667 :=
@BSN.binarySplit_of_base11 (BSN.artanhP 20665953566760000) (BSN.artanhQ 62608993566760000)
  0 11 p20663 p20662 p20664
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p20668 :=
p20661 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p20666 (p20667 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

noncomputable def p20669 :=
@p20657 625289 17000000000000000 57294810192005142115441
  18014398509481984000 637959231007 68000000000000000000
  (Enclosure.Real.IsNear.const false 102026300 400000)
  (BSN.isNear_log_sfrac 41637473566760000 160000000000 56156902869167207
    4503599627370496 625289 17000000000000000 false
    (@p20659 1000462400000000 p20660 56156902869167207
      4503599627370496 625289 17000000000000000
      (p20668 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p20670 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 1 4)
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 1 2) Real.pi)
    (Real.arctan
      (@HDiv.hDiv Real Real Real c4
        (@Nat.cast Real Real.instNatCast 100000)
        (@Nat.cast Real Real.instNatCast 204052600))))
  1 4

noncomputable def p20671 :=
@p20670 0 1 884003834332579 562949953421312 10000017
  34000000000000000 884003834332579 2251799813685248 10000017
  136000000000000000 (Enclosure.Real.IsNear.const false 1 4)

noncomputable def p20672 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 1 2) Real.pi)
  (Real.arctan
    (@HDiv.hDiv Real Real Real c4
      (@Nat.cast Real Real.instNatCast 100000) (@Nat.cast Real Real.instNatCast 204052600)))
  884279719003555 562949953421312 1

noncomputable def p20673 :=
nat_lit 7593535115994057584672768

noncomputable def p20674 :=
@p20672 2000000000000000 4209666 8589934592 1
  3400000000 p20673 884003834332579 562949953421312 10000017
  34000000000000000
  (@p803 1 1000000000000000 884279719003555 562949953421312
    1 2000000000000000 (Enclosure.Real.IsNear.const false 1 2)
    BSN.pi_near_15 (Eq.refl true))

noncomputable def p20675 :=
BSN.arctan_dyadic_bound_f 100000 204052600 1 0 8589934592
  3400000000 0 1 1 0 1

noncomputable def p20676 :=
p20675 1 4209666 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)
  (@BSN.binarySplit_of_le (BSN.arctanEvenP 100000) (BSN.arctanEvenQ 204052600) 0
    0 (Eq.refl true))
  (@BSN.binarySplit_of_le (BSN.arctanOddP 100000) (BSN.arctanOddQ 204052600) 0 0
    (Eq.refl true))

noncomputable def p20677 :=
p20671
  (p20674
    (p20676 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p20678 :=
@p20649 80259232491973617 137438953472000 1020263
  68719476736000 p20650 37578287906902706835121 18014398509481984000
  866407062541942891 p20639
  (@p20652 1 p20653 9619605205618134552509
    3602879701896396800 642959239507 68000000000000000000
    (@p20656 68000000000000000000 p20669 p20677
      (Eq.refl true) (Eq.refl true))
    (Enclosure.Real.IsNear.const false 102026300 200000) (Eq.refl true)
    (Eq.refl true))

noncomputable def p20679 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 102026300 200000) (Real.log Real.pi)
  102026300 200000 0 1 78665238759 68719476736

noncomputable def p20680 :=
p20678
  (@p20679 1 34359738368 80259232491973617 137438953472000
    1020263 68719476736000
    (Enclosure.Real.IsNear.const false 102026300 200000) d258
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p20681 :=
@p20635 2147483648 209 8589934592 false 17179753970
  17179869184 1 3400000000
  (@p20638 866407062541942891 p20639 4479680653111
    2147483648 209 8589934592
    (@p20643 p20636 p20637 866407062541942891
      p20639
      (p20645 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p20648 (p20680 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p20641 p20642)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p20682 :=
nat_lit 485004480890731260240986112

noncomputable def p20683 :=
BSN.cos_reduce3
  (@HDiv.hDiv Real Real Real c4
    (@Nat.cast Real Real.instNatCast 4479680653111)
    (@Nat.cast Real Real.instNatCast 2147483648))
  (@HDiv.hDiv Real Real Real c4
    (@Nat.cast Real Real.instNatCast p20682)
    (@Nat.cast Real Real.instNatCast p976))
  226375608064910080 72057594037927936 false

noncomputable def p20684 :=
BSN.sin_reduce_arg_pos_rat_q3 4479680653111 2147483648 226375608064910080
  72057594037927936 331 p20682 p976
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p20685 :=
nat_lit
  1128721813046508988344401483824115000029600669993772673691393647372447147473805579909207794824792337519335682980885104774946951624339647176108094910813785349981274493416961

noncomputable def p20686 :=
nat_lit
  789716568041567661311733099041525649626948998765635226462717336247741773660064658064387607566234029099167065204677214690878464436035017851033878115681942938230453761

noncomputable def p20687 :=
nat_lit
  5636661258417195377480597625113601187621632665135747509397967959699821245602226720479816606217317058354696726629910051604541312808819832927301886630282460470373925282117121

noncomputable def p20688 :=
BSN.sin_dyadic_bound_f 55138625713281 35184372088832 4 3 17179869184
  6806640626 p20685 p3100 p20686
  p20687 p3103

noncomputable def p20689 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 55138625713281) (BSN.sinEvenQ 35184372088832) 0
  3 p20685 p3100 p20686 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20690 :=
p20688 p20686 17179753970 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p20689 (Eq.refl true))

noncomputable def p20691 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 55138625713281) (BSN.sinOddQ 35184372088832) 0
  3 p20687 p3103 p20686 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20692 :=
@BSN.sin_arg_round false 17179753970 17179869184 p20682
  p976 55138625713281 35184372088832 6806640626 6800000000
  (p20690 (p20691 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p20693 :=
p20683 17179753970 17179869184 331 1000000000000000
  6800000000 3400000000 p20684 BSN.pi_near_15 p20692
  (Eq.refl true) (Eq.refl true)

noncomputable def p20694 :=
@p20633 8589934592 1404667841 57042534400000000
  (BSN.main_sum_rs_one
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 102026300
        true 5))
    (@OfScientific.ofScientific Real c2 102026300
      true 5))
  (@p20634 17179869184 719189934592 29205777612800000000
    8589876985 8589934592 1404667841 57042534400000000
    (p20681 (Enclosure.sfrac_false_div 4479680653111 2147483648)
      (p20693 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p20695 :=
@p20631 false 8589876985 8589934592 1404667841
  57042534400000000 137438031760 137438953472 3385 137438953472
  p20694 (Eq.refl true)

noncomputable def p20696 :=
p20630 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 614 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 107604138004 137438953472)
  (Enclosure.sfrac_ofScientific_eq 102026300 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true) p20695
  (@p20638 866407062541942891 p20639 286699561799107
    137438953472 3341 137438953472
    (@p20643 p20636 p20637 866407062541942891
      p20639
      (p20645 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p20648 (p20680 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p20641 p20642)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p20697 :=
nat_lit
  5453619683685921191908130566684784983337531958910460562926520407424221428222371816512091558617796555891188841834383731589338604304293197177041

noncomputable def p20698 :=
nat_lit
  561210038471690834956592332584953176667568923547197580361530336984724680038811529982632466335663293364651750318403029958467084645753041

noncomputable def p20699 :=
nat_lit
  27255219812090939766661214862561475811218731287575823093382051761134490710914985646801757802929054530687051143702726849012103364226338928648401

noncomputable def p20700 :=
BSN.sin_dyadic_bound_f 169470373221 137438953472 4 3 137438953472
  68719476736 p20697 p2504 p20698
  p20699 p2507

noncomputable def p20701 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 169470373221) (BSN.sinEvenQ 137438953472) 0
  3 p20697 p2504 p20698 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20702 :=
p20700 p20698 129674601963 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p20701 (Eq.refl true))

noncomputable def p20703 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 169470373221) (BSN.sinOddQ 137438953472) 0
  3 p20699 p2507 p20698 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20704 :=
nat_lit
  184306086751199152949588824163283918331243354730716405744081325266459148579255866857965110015356142942850009352917492648391858380084153942016

noncomputable def p20705 :=
nat_lit
  381459200526006571702654598144805937183466045378631148662835886794429966404721675452156972319926837545120708553802566699354880475136

noncomputable def p20706 :=
nat_lit
  1118033417287319125108888427171996364569864052364648075951286302939526070381198687855774575737849319336075117377489584667593894854544850944000

noncomputable def p20707 :=
BSN.cos_dyadic_bound_f 92282781156 137438953472 4 3 137438953472
  68719476736 p20704 p2457 p20705
  p20706 p2460

noncomputable def p20708 :=
@BSN.binarySplit_of_base3 (BSN.cosEvenP 92282781156) (BSN.cosEvenQ 137438953472) 0
  3 p20704 p2457 p20705 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20709 :=
p20707 p20705 107604138004 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p20708 (Eq.refl true))

noncomputable def p20710 :=
@BSN.binarySplit_of_base3 (BSN.cosOddP 92282781156) (BSN.cosOddQ 137438953472) 0
  3 p20706 p2460 p20705 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20711 :=
p20696 d93 d95 d97 d99 d103
  (p20702 (p20703 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p20709 (p20710 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p20712 :=
p20626 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 282 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 74334581550 137438953472)
  (Enclosure.sfrac_ofScientific_eq 102026300 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p20711 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p20638 866407062541942891 p20639 286699561799107
    137438953472 3341 137438953472
    (@p20643 p20636 p20637 866407062541942891
      p20639
      (p20645 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p20648 (p20680 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p20641 p20642)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p20713 :=
nat_lit
  1539995807732995721634013170066723810788841284014219696327294518715377608176161083856974931236864884368887997955406331020607147775989934718976

noncomputable def p20714 :=
nat_lit
  12657381477804152070038293605954678717378569061272517527876148275257947693675617529665755388828461596513564236978466807483860596555776

noncomputable def p20715 :=
nat_lit
  7698951116625055327253601865572100891077981873386858312518485601851931423611432973306988399855534065300226858801976557879530704625144782913536

noncomputable def p20716 :=
BSN.sin_dyadic_bound_f 123555473424 137438953472 4 3 137438953472
  68719476736 p20713 p2504 p20714
  p20715 p2507

noncomputable def p20717 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 123555473424) (BSN.sinEvenQ 137438953472) 0
  3 p20713 p2504 p20714 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20718 :=
p20716 p20714 107572807935 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p20717 (Eq.refl true))

noncomputable def p20719 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 123555473424) (BSN.sinOddQ 137438953472) 0
  3 p20715 p2507 p20714 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20720 :=
nat_lit
  904814179241023677212823676476559878547433423736612145500347690871772716710101495609475034849164862006174947673292596761635559251843194390625

noncomputable def p20721 :=
nat_lit
  45070414501695364892928287731569209999858878752818299204081507152420078645248894457085343284913336896052250427962155244140566650390625

noncomputable def p20722 :=
nat_lit
  5487034546322721733577981168884485994696198915292761085386418548571840724176513948242577492358038734247448260884119692590373870045540883990625

noncomputable def p20723 :=
BSN.cos_dyadic_bound_f 137348618665 137438953472 4 3 137438953472
  68719476736 p20720 p2457 p20721
  p20722 p2460

noncomputable def p20724 :=
@BSN.binarySplit_of_base3 (BSN.cosEvenP 137348618665) (BSN.cosEvenQ 137438953472) 0
  3 p20720 p2457 p20721 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20725 :=
p20723 p20721 74334581550 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p20724 (Eq.refl true))

noncomputable def p20726 :=
@BSN.binarySplit_of_base3 (BSN.cosOddP 137348618665) (BSN.cosOddQ 137438953472) 0
  3 p20722 p2460 p20721 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20727 :=
p20712 d105 d107 d109 d111 d103
  (p20718 (p20719 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p20725 (p20726 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p20728 :=
p20621 BSN.abs_quadSignPos (BSN.cos_quad_nat0 64 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 136040633432 137438953472)
  (Enclosure.sfrac_ofScientific_eq 102026300 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p20727 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p20638 866407062541942891 p20639 286699561799107
    137438953472 3341 137438953472
    (@p20643 p20636 p20637 866407062541942891
      p20639
      (p20645 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p20648 (p20680 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p20641 p20642)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p20729 :=
nat_lit 2770903861354727594931161652905519504939225944270728062676079693978470087364843884269895936

noncomputable def p20730 :=
nat_lit 21366773089067664030882171710909052209306980075309036415920557001452320674025035366656

noncomputable def p20731 :=
nat_lit 8312668850518004649465423194373136696713259218852033569955407240821407357453183602738954496

noncomputable def p20732 :=
BSN.cos_dyadic_bound_f 46367893602 137438953472 3 2 137438953472
  68719476736 p20729 p2466 p20730
  p20731 p2469

noncomputable def p20733 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP 46367893602) (BSN.cosEvenQ 137438953472) 0
  2 p20729 p2466 p20730 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20734 :=
p20732 p20730 129691272392 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p20733 (Eq.refl true))

noncomputable def p20735 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP 46367893602) (BSN.cosOddQ 137438953472) 0
  2 p20731 p2469 p20730 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20736 :=
nat_lit 88862226493648945844126038125569092900115083652837042607117792836957288748744528764066401

noncomputable def p20737 :=
nat_lit 21975404926571672298664511231529583622590068206299604937744279213017748775897127521

noncomputable def p20738 :=
nat_lit 266586635530136984389033517047684815641178005778374715222143503022313440210736034497944161

noncomputable def p20739 :=
BSN.cos_dyadic_bound_f 19621947563 137438953472 3 2 137438953472
  68719476736 p20736 p2466 p20737
  p20738 p2469

noncomputable def p20740 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP 19621947563) (BSN.cosEvenQ 137438953472) 0
  2 p20736 p2466 p20737 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20741 :=
p20739 p20737 136040633432 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p20740 (Eq.refl true))

noncomputable def p20742 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP 19621947563) (BSN.cosOddQ 137438953472) 0
  2 p20738 p2469 p20737 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20743 :=
p20728 d113 d115 d117 d119 d103
  (p20734 (p20735 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p20741 (p20742 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p20744 :=
p20616 BSN.abs_quadSignPos (BSN.cos_quad_nat3 99 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 30562063100 137438953472)
  (Enclosure.sfrac_ofScientific_eq 102026300 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p20743 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p20638 866407062541942891 p20639 286699561799107
    137438953472 3341 137438953472
    (@p20643 p20636 p20637 866407062541942891
      p20639
      (p20645 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p20648 (p20680 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p20641 p20642)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p20745 :=
nat_lit
  928762787811099807803732380695062511417933405964080544110973656628363688856032585978669067800808797436486334289444726921495443481295103140625

noncomputable def p20746 :=
nat_lit
  48742446862767269375902916629095193352813522825172251766075169659887011269862027878157953721612536646764864105014171468181797119140625

noncomputable def p20747 :=
nat_lit
  5632206366768575257095072705225285320853023488662135900659986464575166946586373128395058007470374850466897963143548036883135404217832088740625

noncomputable def p20748 :=
BSN.cos_dyadic_bound_f 138248027605 137438953472 4 3 137438953472
  68719476736 p20745 p2457 p20746
  p20747 p2460

noncomputable def p20749 :=
@BSN.binarySplit_of_base3 (BSN.cosEvenP 138248027605) (BSN.cosEvenQ 137438953472) 0
  3 p20745 p2457 p20746 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20750 :=
p20748 p20746 73576488316 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p20749 (Eq.refl true))

noncomputable def p20751 :=
@BSN.binarySplit_of_base3 (BSN.cosOddP 138248027605) (BSN.cosOddQ 137438953472) 0
  3 p20747 p2460 p20746 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20752 :=
nat_lit 973499257275154112901331880314716691973283385703211837018359834294220929695779207064530625

noncomputable def p20753 :=
nat_lit 814007174225674874633631132608169118641725313975037874797869871501095568603687890625

noncomputable def p20754 :=
nat_lit 2549639593994740596982262660659567113370502495000760756415335607552691433143739231579090625

noncomputable def p20755 :=
BSN.sin_dyadic_bound_f 30819708665 137438953472 3 2 137438953472
  68719476736 p20752 p2477 p20753
  p20754 p2480

noncomputable def p20756 :=
@BSN.binarySplit_of_base2 (BSN.sinEvenP 30819708665) (BSN.sinEvenQ 137438953472) 0
  2 p20752 p2477 p20753 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20757 :=
p20755 p20753 30562063100 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p20756 (Eq.refl true))

noncomputable def p20758 :=
@BSN.binarySplit_of_base2 (BSN.sinOddP 30819708665) (BSN.sinOddQ 137438953472) 0
  2 p20754 p2480 p20753 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20759 :=
p20744 d121 d123 d125 d127 d103
  (p20750 (p20751 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p20757 (p20758 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p20760 :=
p20611 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 229 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 94445890303 137438953472)
  (Enclosure.sfrac_ofScientific_eq 102026300 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p20759 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p20638 866407062541942891 p20639 286699561799107
    137438953472 3341 137438953472
    (@p20643 p20636 p20637 866407062541942891
      p20639
      (p20645 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p20648 (p20680 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p20641 p20642)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p20761 :=
nat_lit
  1585338832002044849615675065356952609607863327066771131919934688321416805025490056635745362731275743541882282641388977843276484737531113373696

noncomputable def p20762 :=
nat_lit
  13808396967747853931778926750342330702467866403495604660705655131598887408891501761443743124923556273220685321896392536339646404100096

noncomputable def p20763 :=
nat_lit
  7925604827653202907834051313371676554217482030771117248728442940623633602870840484756194614512111292223025038045282424223839115612905753542656

noncomputable def p20764 :=
BSN.sin_dyadic_bound_f 124454882364 137438953472 4 3 137438953472
  68719476736 p20761 p2504 p20762
  p20763 p2507

noncomputable def p20765 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 124454882364) (BSN.sinEvenQ 137438953472) 0
  3 p20761 p2504 p20762 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20766 :=
p20764 p20762 108130297364 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p20765 (Eq.refl true))

noncomputable def p20767 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 124454882364) (BSN.sinOddQ 137438953472) 0
  3 p20763 p2507 p20762 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20768 :=
nat_lit
  776673216704340831135486848308716153400250411029675586464183891975847658000586339786525393411015793109398471296880340763228866639703159934976

noncomputable def p20769 :=
nat_lit
  1624200700551842195643138224009832616863718573399271074093015830470855611288641357436763017959907732539784813348445519804149432651776

noncomputable def p20770 :=
nat_lit
  3883104578444241568158482881604996048810686098542404116060448253368673170010217876836939269068824920135260854547898515800128477613626141249536

noncomputable def p20771 :=
BSN.sin_dyadic_bound_f 104124590826 137438953472 4 3 137438953472
  68719476736 p20768 p2504 p20769
  p20770 p2507

noncomputable def p20772 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 104124590826) (BSN.sinEvenQ 137438953472) 0
  3 p20768 p2504 p20769 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20773 :=
p20771 p20769 94445890303 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p20772 (Eq.refl true))

noncomputable def p20774 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 104124590826) (BSN.sinOddQ 137438953472) 0
  3 p20770 p2507 p20769 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20775 :=
p20760 d129 d131 d133 d135 d103
  (p20766 (p20767 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p20773 (p20774 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p20776 :=
p20606
  (p20775 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p20638 866407062541942891 p20639 286699561799107
    137438953472 3341 137438953472
    (@p20643 p20636 p20637 866407062541942891
      p20639
      (p20645 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p20648 (p20680 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p20641 p20642)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p20777 :=
nat_lit
  290630856142428045199410398638836742883141854608880134090974858609315925844322483702261370278589291318286930396258899039713884844729083182153707331671828475919430506434441686691206716593340416

noncomputable def p20778 :=
nat_lit
  5765353595857776242624860871642479886919875261061710514480556676432029053838785212846868915030614583352860005060453947473989179403103839466467660368207274948480973235352179792670708534870016000

noncomputable def p20779 :=
nat_lit
  21531765294251566378719684202093821276560485047661748869487960091250970461027293330614860404745639767728341291242949574338806332029033277204965261980791413358640042869411123938000896

noncomputable def p20780 :=
nat_lit
  2363649359913947215347933968035459088852310437352120418594204845815650588187393412017476856145768985232130429010527148124338085425374379439969846974595581630828604208151822807537931871221514240

noncomputable def p20781 :=
nat_lit
  328625154963893245829617069683621353554432889880517499325391730556625656068810757132271528156745031251113020288445875006017383225976918849588656640987814672063415474415074248182230386487590912000

noncomputable def p20782 :=
BSN.sin_dyadic_bound_f 215435603346 137438953472 5 4 137438953472
  68719476736 p20777 p20778 p20779
  p20780 p20781

noncomputable def p20783 :=
@BSN.binarySplit_of_base4 (BSN.sinEvenP 215435603346) (BSN.sinEvenQ 137438953472) 0
  4 p20777 p20778 p20779 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20784 :=
p20782 p20779 137438206926 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p20783 (Eq.refl true))

noncomputable def p20785 :=
@BSN.binarySplit_of_base4 (BSN.sinOddP 215435603346) (BSN.sinOddQ 137438953472) 0
  4 p20780 p20781 p20779 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20786 :=
p20776 d137 d139 d103
  (p20784 (p20785 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true) (Eq.refl true)

noncomputable def p20787 :=
@p20595 p20588 p20589 p20588
  (p20599
    (@p20602 218955 68719476736
      (p20786 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (p20786 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true) (Eq.refl true)))

noncomputable def p20788 :=
nat_lit
  1663261795844368081340811904444341776332177406149614818131651448544198824512325996696237887201110712309808678640783363752965335213734099408800662928338345917548381047148737549537627364913821862428315295352027208807192327688342789927192570523173505059772517775867791066982918130177412940095461416518830189871997549725

noncomputable def p20789 :=
nat_lit
  12064114410120881697684249086315471354100504503497011563593230129923244688987454586741947156276531487416450850028801674329627080999958126358211839195533902044386710183415792069701368078118158360793576698212191168580174892152827542937880954483101341506291035205862448784848059094859987648259778470316291228729945882624

noncomputable def p20790 :=
nat_lit
  435055752109204268169900363565905341701407234045958544554398928287919783289702302094955245736902444847770106560574917954993633538886382519784171700128194289826963954882334497632555370840101673928718430672531714563654830210315509737394897381223779735635220723431134822246509718660697311278313563712428302819254905

noncomputable def p20791 :=
nat_lit
  1544206644495472857303583883048380333324864576447617480139933456630175320190394187102969236003396030389305708803686614314192266367994640173851115417028339461681498903477221384921775113999124270181577817371160469578262386195561925496048762173836971712805252506350393444460551564142078418977251644200485277277433072975872

noncomputable def p20792 :=
@Enclosure.Real.IsNear.mulLit_ff p20582
  (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
        (Enclosure.sfrac false 12 1)))
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Zeta.RiemannSiegel.correctionLinear
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
          (Enclosure.sfrac false 12 1)))
      (@Inv.inv Real Real.instInv p20583)))

noncomputable def p20793 :=
nat_lit
  345600073994808001321300988575271860826301358706071299510491090279406176108167483637506340204980382651911058669819474131181863084812565337220302943281454165292724738165810004432720899551264901238019304726044867891680654208141221653034962893833792824848933944298800095417840006822757404831647306131052078925

noncomputable def p20794 :=
nat_lit
  702223880805592151456759840151962786569522257399338504974336254522393264865238137237142489540654437582500444843247630303354647534431314931612685275935445798350655833690880801860555545317367555154113605281582053784524026102900245630757473088050106395169337932361665227499793929447186391815763110662594625536

noncomputable def p20795 :=
nat_lit
  180777328284176241289898896297714160785115195581267176797915094256021068402041046287994244739713470739985477558836552162086111828786359489127222222003267580360251779198108315138478395162136745910920597768524357177757723171042874527147829719496075937022202220614265514550430488072382226429826490186122545

noncomputable def p20796 :=
@p20792 4812677777 17179869184 1 17179869184
  p20793 p20794 p20795 p20578
  p20788 p20789 p20790

noncomputable def p20797 :=
@Enclosure.Real.IsNear.mulLit_ff
  c22
  (p20581
    (@Neg.neg Real Real.instNeg
      (@HDiv.hDiv Real Real Real c4
        c37
        c20)))

noncomputable def p20798 :=
@p20797 1 1 0 1 4812677777 17179869184
  1 17179869184 4812677777 17179869184 1

noncomputable def p20799 :=
@Enclosure.Real.IsNear.of_eq
  (p20581
    (@Neg.neg Real Real.instNeg
      (@HDiv.hDiv Real Real Real c4
        c37
        c20)))

noncomputable def p20800 :=
BSN.rpow_neg_quarter_mk
  (@HDiv.hDiv Real Real Real c4
    (@OfScientific.ofScientific Real c2 102026300
      true 5)
    c7)

noncomputable def p20801 :=
p20800
  (BSN.t_div_two_pi_nonneg
    (@OfScientific.ofScientific Real c2 102026300
      true 5)
    102026300 100000
    (Enclosure.sfrac_ofScientific_eq 102026300 5 100000 (Eq.refl true)))

noncomputable def p20802 :=
@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt p20583)) false
  4812677777 17179869184 1 17179869184 4812677777
  17179869184

noncomputable def p20803 :=
@Enclosure.Real.IsNear.recentre' (Real.sqrt p20583) false 61327169377
  17179869184 7 17179869184 61327169377 17179869184 7
  17179869184

noncomputable def p20804 :=
@Enclosure.Real.IsNear.sqrt_image
  (@HDiv.hDiv Real Real Real c4
    (@OfScientific.ofScientific Real c2 102026300
      true 5)
    c7)

noncomputable def p20805 :=
@Enclosure.Real.IsNear.of_eq
  (@HDiv.hDiv Real Real Real c4
    (@OfScientific.ofScientific Real c2 102026300
      true 5)
    c7)

noncomputable def p20806 :=
@p20805
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 102026300 100000)
    (@Inv.inv Real Real.instInv
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)))
  false 2789665435730089

noncomputable def p20807 :=
@p20806 17179869184000 1020263 17179869184000
  (BSN.t_div_two_pi_mk
    (@OfScientific.ofScientific Real c2 102026300
      true 5)
    102026300 100000
    (Enclosure.sfrac_ofScientific_eq 102026300 5 100000 (Eq.refl true)))

noncomputable def p20808 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 102026300 100000)
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi))
  102026300 100000 0

noncomputable def p20809 :=
@p20808 1 2734261103 17179869184 1 17179869184
  2789665435730089 17179869184000 1020263 17179869184000
  (Enclosure.Real.IsNear.const false 102026300 100000) d261

noncomputable def p20810 :=
@p20804 2789665435730089 17179869184000 1020263 17179869184000
  109460137990 109460138031 8589934592
  (p20807 (p20809 (Eq.refl true))) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20811 :=
@Enclosure.Real.IsNear.recentre' p20583 false 218920276021 17179869184
  41 17179869184 218920276021 17179869184 41 17179869184
  (p20810 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p20812 :=
@Enclosure.Real.IsNear.sqrt_image p20583 218920276021 17179869184 41
  17179869184 30663584685 30663584692 8589934592
  (p20811 (Eq.refl true)) (Eq.refl true) (Eq.refl true)

noncomputable def p20813 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt p20583) 61327169377 17179869184
  7 17179869184 2406338888 2406338889 8589934592
  (p20803
    (p20812 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p20814 :=
@p20799 (@Inv.inv Real Real.instInv (Real.sqrt p20583)) false
  4812677777 17179869184 1 17179869184 p20801
  (@p20802 1 17179869184
    (p20813 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p20815 :=
@Enclosure.Real.IsNear.recentre'
  (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
        (Enclosure.sfrac false 12 1)))
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Zeta.RiemannSiegel.correctionLinear
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
          (Enclosure.sfrac false 12 1)))
      (@Inv.inv Real Real.instInv p20583)))

noncomputable def p20816 :=
nat_lit
  122928583233239844077131249482445629333878332995261680222582264094094326513387911475836086423005160103190124740008855470218556043574724452606511110962221954644971209854713654294165308710252987219426006482596562880875251756309154678460524209257331637175097510017700549894292731889219913972282013326563330572296149

noncomputable def p20817 :=
nat_lit
  122243133170637481725592752973653681886022434568076846945932455187258219547740654930241764579237124494361677438312547483207977042793803303295136252834842404576882167528908529987885509328847344001228096407417803922809942463992874759402260915167762521271078347265518682803164127238166207087288042304144472413306880000000

noncomputable def p20818 :=
@Enclosure.Real.IsNear.addLit_ft_p
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
      (Enclosure.sfrac false 12 1)))
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Zeta.RiemannSiegel.correctionLinear
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
        (Enclosure.sfrac false 12 1)))
    (@Inv.inv Real Real.instInv p20583))
  72748525240649806875

noncomputable def p20819 :=
nat_lit 97998327891581992960000000

noncomputable def p20820 :=
nat_lit
  570444724132942466153295868632881414263763399418593190907714850061934593883381429923785065040758620601024216128697004871668562144651564554000883982675899448950110011063193146331990373887047925049076136114868071358506321506510942217810685730500602106667820493247257292516011935241757035343904326937041075

noncomputable def p20821 :=
nat_lit
  123231213321984159639552479325266209012280696496993538856446535228847416889148242331674641106178657777640433091057643108796083455783415964501535394673145281906181832191916167343434559397882917966422243304677564587019581822793850217491260608588317135178837845122355794914954103448065088532587762612590265

noncomputable def p20822 :=
nat_lit
  92041888504950574475740425768398066361240421321846096523996201552759130012416493123946740389072658442813498306494153399121300361632981310716337884487410751681417161433531128461466736435838000189159978471467522953645133149359340995314643512596903545427635461470508184698852989920501614748075702440767602758254592

noncomputable def p20823 :=
nat_lit
  51001568934698456177115366180777569317817897261693575341867583044078662041154298235675403123918317285344815563196876044614376605143311783136106963250974965566797156156752132332177002765237827632951493257858128430563917498590720880195406147229828762117694427933145350697722737591077298329324720394989304417371253375251146342400

noncomputable def p20824 :=
@p20818 147573952589676412928 98416624770278259333 p20819
  p20820 p20794 p20821 p20822
  p20823 p20793 p20794 p20816

noncomputable def p20825 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  (@Inv.inv Real Real.instInv
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
          (Enclosure.sfrac false 12 1)))))

noncomputable def p20826 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
        (Enclosure.sfrac false 12 1))
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
        (Enclosure.sfrac false 12 1)))
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
      (Enclosure.sfrac false 12 1)))

noncomputable def p20827 :=
@Enclosure.Real.IsNear.of_eq
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
      (Enclosure.sfrac false 12 1)))
  (p20825
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p20826 (Enclosure.sfrac false 1 16)))))

noncomputable def p20828 :=
BSN.cos_two_pi_p_ne_zero_mk
  (@OfScientific.ofScientific Real c2 102026300
    true 5)
  102026300 100000 12
  (Enclosure.sfrac_ofScientific_eq 102026300 5 100000 (Eq.refl true))

noncomputable def p20829 :=
@Enclosure.Real.IsNear.mulLit_tt
  (@Inv.inv Real Real.instInv
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
          (Enclosure.sfrac false 12 1)))))

noncomputable def p20830 :=
@p20829
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p20826 (Enclosure.sfrac false 1 16))))
  381859321175

noncomputable def p20831 :=
@p20830 17179869184 130455 17179869184 190511325
  8589934592 4290195057 114085068800000000 72748525240649806875
  147573952589676412928 98416624770278259333 p20819

noncomputable def p20832 :=
@Enclosure.Real.IsNear.of_eq
  (@Inv.inv Real Real.instInv
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
          (Enclosure.sfrac false 12 1)))))

noncomputable def p20833 :=
@Inv.inv Real Real.instInv
  (@Neg.neg Real Real.instNeg
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
          (Enclosure.sfrac false 12 1)))))

noncomputable def p20834 :=
@p20832 (@Neg.neg Real Real.instNeg p20833) true 381859321175
  17179869184 130455 17179869184
  (BSN.inv_eq_neg_inv_neg
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
          (Enclosure.sfrac false 12 1)))))

noncomputable def p20835 :=
@Enclosure.Real.IsNear.inv_image
  (@Neg.neg Real Real.instNeg
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
          (Enclosure.sfrac false 12 1)))))

noncomputable def p20836 :=
@Enclosure.Real.IsNear.neg
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
        (Enclosure.sfrac false 12 1))))
  true

noncomputable def p20837 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
        (Enclosure.sfrac false 12 1))))
  true

noncomputable def p20838 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
      (Enclosure.sfrac false 12 1)))
  (@HDiv.hDiv Real Real Real c4
    (@Nat.cast Real Real.instNatCast 10023130263)
    (@Nat.cast Real Real.instNatCast 2147483648))
  false

noncomputable def p20839 :=
nat_lit 11285041429486334908865215

noncomputable def p20840 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
      (Enclosure.sfrac false 12 1)))
  false p20839

noncomputable def p20841 :=
nat_lit 1106429201394226670520990943

noncomputable def p20842 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
    (Enclosure.sfrac false 12 1))
  884279719003555 140737488355328 1

noncomputable def p20843 :=
@Enclosure.Real.IsNear.subLit_ff_p p20583 (Enclosure.sfrac false 12 1)
  218920276021 17179869184 41 17179869184 12 1 0

noncomputable def p20844 :=
@p20842 500000000000000 12761845813 17179869184 41
  17179869184 p20839 p2602 p20841
  p5018 d260
  (@p20843 1 12761845813 12761845813 17179869184 41
    17179869184 (p20811 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p20845 :=
@p20838 10023130263 2147483648 259 17179869184 true
  772923139 17179869184 1 3400000000
  (@p20840 p2602 p20841 p5018
    10023130263 2147483648 259 17179869184
    (p20844 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div 10023130263 2147483648)

noncomputable def p20846 :=
nat_lit 472209469710145091488710656

noncomputable def p20847 :=
BSN.cos_reduce2
  (@HDiv.hDiv Real Real Real c4
    (@Nat.cast Real Real.instNatCast 10023130263)
    (@Nat.cast Real Real.instNatCast 2147483648))
  (@HDiv.hDiv Real Real Real c4
    (@Nat.cast Real Real.instNatCast p20846)
    (@Nat.cast Real Real.instNatCast p976))
  226375608064910080 72057594037927936 false

noncomputable def p20848 :=
BSN.sin_reduce_arg_pos_rat_q2 10023130263 2147483648 226375608064910080
  72057594037927936 0 p20846 p976 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p20849 :=
nat_lit
  26144778254679382956050786225287011092693703816444269256035551616932202141936424476457903062580085056722268445259159317135759576206796693858287283668925861519806352020302962651305519160510483496195088397877256991496403384193054401

noncomputable def p20850 :=
nat_lit
  4759025789102335498334892829692112005846947786644249548113389465792667896841339666088051780031891201623678092723172321101010502794836131356280901565056936692681796004281896597179499764063615318160103591718425007117629121

noncomputable def p20851 :=
nat_lit
  266104715029347883523268111830097616017009772800888658399650107993157997680652816200861308369091214653957152683475538297020878110433187352678662533882696601810250935139902174838027843770249835767287095115491417107071804298489558721

noncomputable def p20852 :=
BSN.cos_dyadic_bound_f 53684001353547 35184372088832 5 4 17179869184
  6806640626 p20849 p12328 p20850
  p20851 p12330

noncomputable def p20853 :=
@BSN.binarySplit_of_base4 (BSN.cosEvenP 53684001353547) (BSN.cosEvenQ 35184372088832) 0
  4 p20849 p12328 p20850 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20854 :=
p20852 p20850 772923139 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p20853 (Eq.refl true))

noncomputable def p20855 :=
@BSN.binarySplit_of_base4 (BSN.cosOddP 53684001353547) (BSN.cosOddQ 35184372088832) 0
  4 p20851 p12330 p20850 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20856 :=
@BSN.cos_arg_round false 772923139 17179869184 p20846 p976
  53684001353547 35184372088832 6806640626 6800000000
  (p20854 (p20855 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p20857 :=
p20847 772923139 17179869184 0 1000000000000000
  6800000000 3400000000 p20848 BSN.pi_near_15 p20856
  (Eq.refl true) (Eq.refl true)

noncomputable def p20858 :=
@p20836 772923139 17179869184 1753476307 114085068800000000
  (@p20837 772923139 17179869184 897779869184
    58411555225600000000 772923139 17179869184 1753476307
    114085068800000000
    (p20845 (p20857 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p20859 :=
@p20835 772923139 17179869184 1753476307 114085068800000000
  190929595360 190929725815 8589934592 p20858
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p20860 :=
@Enclosure.Real.IsNear.recentre' p20833 false 381859321175 17179869184
  130455 17179869184 381859321175 17179869184 130455
  17179869184
  (p20859 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p20861 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p20826 (Enclosure.sfrac false 1 16))))
  true

noncomputable def p20862 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p20826 (Enclosure.sfrac false 1 16)))
  (@HDiv.hDiv Real Real Real c4
    (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 13683564651))
    (@Nat.cast Real Real.instNatCast 8589934592))
  true

noncomputable def p20863 :=
nat_lit 66169658444204251918294188318934645

noncomputable def p20864 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p20826 (Enclosure.sfrac false 1 16)))
  true p20863

noncomputable def p20865 :=
nat_lit 9449692538105286341278886179521587817

noncomputable def p20866 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (p20826 (Enclosure.sfrac false 1 16)) 884279719003555
  140737488355328 1

noncomputable def p20867 :=
@Enclosure.Real.IsNear.subLit_tf
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
        (Enclosure.sfrac false 12 1))
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
        (Enclosure.sfrac false 12 1)))
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
      (Enclosure.sfrac false 12 1)))

noncomputable def p20868 :=
@p20867 (Enclosure.sfrac false 1 16) 56382133058932495623
  295147905179352825856 1750845994891 295147905179352825856 1 16
  0

noncomputable def p20869 :=
@Enclosure.Real.IsNear.subLit_ff_n
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
      (Enclosure.sfrac false 12 1))
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
      (Enclosure.sfrac false 12 1)))
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
    (Enclosure.sfrac false 12 1))
  162864708554785630969

noncomputable def p20870 :=
nat_lit 968637670267342037489792581632

noncomputable def p20871 :=
@p20869 295147905179352825856 1046471358347 295147905179352825856
  12761845813 17179869184 41 17179869184 p20870
  56382133058932495623 295147905179352825856 1750845994891

noncomputable def p20872 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
    (Enclosure.sfrac false 12 1))
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
    (Enclosure.sfrac false 12 1))
  12761845813 17179869184 41

noncomputable def p20873 :=
@p20872 17179869184 12761845813 17179869184 41
  17179869184 162864708554785630969 295147905179352825856 1046471358347
  295147905179352825856
  (@p20843 1 12761845813 12761845813 17179869184 41
    17179869184 (p20811 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p20874 :=
p20873
  (@p20843 1 12761845813 12761845813 17179869184 41
    17179869184 (p20811 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p20875 :=
@p20871 295147905179352825856 (p20874 (Eq.refl true))
  (@p20843 1 12761845813 12761845813 17179869184 41
    17179869184 (p20811 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p20876 :=
@p20866 500000000000000 74828877132642047239 295147905179352825856
  1750845994891 295147905179352825856 p20863 p2630
  p20865 p10041 d260
  (@p20868 1 1197262034122272755824 74828877132642047239
    295147905179352825856 1750845994891 295147905179352825856
    (p20875 (Eq.refl true) (Eq.refl true))
    (Enclosure.Real.IsNear.const false 1 16) (Eq.refl true)
    (Eq.refl true))

noncomputable def p20877 :=
@p20862 13683564651 8589934592 641 17179869184 true
  190511325 8589934592 1 3400000000
  (@p20864 p2630 p20865 p10041
    13683564651 8589934592 641 17179869184
    (p20876 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_true_div 13683564651 8589934592)

noncomputable def p20878 :=
nat_lit
  4951604581610588185910825889930017921087867963794560174670396083413647135192330225868940344697584701510507530293303202336230471774032186535338240634604847072891338785574081

noncomputable def p20879 :=
nat_lit
  1510733902014981489495471152675560747942697981303751410459227390537142762041021848095400916440553127567869816395001479532516758260497601674702999406652565856734401

noncomputable def p20880 :=
nat_lit
  50377714991115319444283265927098797739539732779502012528698711629395131132478753810454124869424800625944220304912649212617280859565620446212814082473019220038412875283320001

noncomputable def p20881 :=
BSN.cos_dyadic_bound_t 13683564651 8589934592 5 4 8589934592
  3400000000 p20878 p2646 p20879
  p20880 p2649

noncomputable def p20882 :=
@BSN.binarySplit_of_base4 (BSN.cosEvenP 13683564651) (BSN.cosEvenQ 8589934592) 0
  4 p20878 p2646 p20879 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20883 :=
p20881 p20879 190511325 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p20882 (Eq.refl true))

noncomputable def p20884 :=
@BSN.binarySplit_of_base4 (BSN.cosOddP 13683564651) (BSN.cosOddQ 8589934592) 0 4
  p20880 p2649 p20879 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20885 :=
p20877
  (BSN.cos_neg_of_bound 13683564651 8589934592 true 190511325 8589934592
    1 3400000000
    (p20883 (p20884 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p20886 :=
p20831
  (p20834
    (@Enclosure.Real.IsNear.neg p20833 false 381859321175 17179869184
      130455 17179869184 (p20860 (Eq.refl true))))
  (@p20861 190511325 8589934592 2196579869184
    58411555225600000000 190511325 8589934592 4290195057
    114085068800000000 (p20885 (Eq.refl true)) (Eq.refl true))

noncomputable def p20887 :=
@p20824 p20817
  (@p20827 false 72748525240649806875 147573952589676412928
    98416624770278259333 p20819
    (BSN.correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
        (Enclosure.sfrac false 12 1))
      (p20828 (Eq.refl true) (Eq.refl true)
        (p20586 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p20886 (Eq.refl true)))

noncomputable def p20888 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Zeta.RiemannSiegel.correctionLinear
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
        (Enclosure.sfrac false 12 1)))
    (@Inv.inv Real Real.instInv p20583))
  true

noncomputable def p20889 :=
nat_lit
  132318507766080370870480261694433628550411513456672252927935776895102882828242439527606342115893649672035425043342191800779737093869108406674597865476902898810937877373409983578428658232519146075708590280136275931544212510123913508511862869924969705817379914021907814408952743912610097431702267667721676392576039

noncomputable def p20890 :=
nat_lit
  98829225247710262867429368515096341332791332892647518728955741224331220492185227974590031104217345944915565363435943316108305047551656971126471386689813725547615929822542168634993607295943953291620980311754270053008792716515963231747120779125566189619536160406425180445475300105093018814544105228831057745755716670455808

noncomputable def p20891 :=
nat_lit
  423116390982353018862121549351008415744370087228339206720372247589855600090745290203749278651650088820828462263551901467577226514690500391685298305875107236705528339519274902841553929301122402652296331757219091869709064642059987660886756575391406405828248207142220811796822190978348540056456025

noncomputable def p20892 :=
nat_lit
  40874809539271061742722513162994453833061401813718170449972167525114099545476384067275939133289179158309733311369062302596555530002300798171938238428873347488153716182038234655079172535180553977500740746128259563383414998120875425564443755897815944345745836172815483732835501982317445323323080704

noncomputable def p20893 :=
@Enclosure.Real.IsNear.mulLit_tf
  (Zeta.RiemannSiegel.correctionLinear
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
      (Enclosure.sfrac false 12 1)))
  (@Inv.inv Real Real.instInv p20583) p20891 p20892

noncomputable def p20894 :=
nat_lit
  392402146460579242144981393122724919827362097833934621470265056303866021599096446310575614157305819208498086415446723693469205247221520654805471645601033715428262470464583223903659990429762362845679415396912435222223167216332605975891492282350970152284875483640485987841981917353431971279943125150171269

noncomputable def p20895 :=
nat_lit
  23010472126237643618935106442099516590310105330461524130999050388189782503104123280986685097268164610703374576623538349780325090408245327679084471121852687920354290358382782115366684108959500047289994617866880738411283287339835248828660878149225886356908865367627046174713247480125403687018925610191900689563648

noncomputable def p20896 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  (@iteratedDeriv Real c11 Real
    Real.normedAddCommGroup
    c8
    (@OfNat.ofNat Nat 3 (instOfNatNat 3)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
      (Enclosure.sfrac false 12 1)))
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 96 1)
      c12))

noncomputable def p20897 :=
@Enclosure.Real.IsNear.of_eq
  (Zeta.RiemannSiegel.correctionLinear
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
      (Enclosure.sfrac false 12 1)))
  (@Neg.neg Real Real.instNeg p20896) true p20891

noncomputable def p20898 :=
nat_lit
  6903211564762685432746639253465591173376991953496889910136536487021376311843835330780127730650083708809166382829263042534598923550425194822770712410979295525100576541694160375547761105303561557909006680187444300411564014009089637273223675073879305412344544778928416109885710134707671818273451963433044725544071580375

noncomputable def p20899 :=
nat_lit
  404804506614621236704990693437834614099113299528284236713802716054860679135990693783920767402874248990374155728633623822779617474771586953734026799881477019843034848553132722728933815484186432682479535356945490137124014966849385397236206711298319112681620113024717539104666829230461005064372655017292012526615415482186989568

noncomputable def p20900 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@iteratedDeriv Real c11 Real
    Real.normedAddCommGroup
    c8
    (@OfNat.ofNat Nat 3 (instOfNatNat 3)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
      (Enclosure.sfrac false 12 1)))
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 96 1)
      c12))

noncomputable def p20901 :=
nat_lit
  22254152625289098696772881140012149005217496410794109977046555690918455869393848289927632039822974035547472893753230802456119994084909938082782873572053111765188320151967007773464034780878809721992637135141355994836592792995356469618443259598055348688339404020557517828365984822725

noncomputable def p20902 :=
nat_lit
  2269007733883335972287082669296112915239349672942191252221331572442536403137824056312817862695551072066953619064625508194663368599769448406663254670871573830845597595897613333042429214224697474472410882236254024057110212260250671521235807709272244389361641091086035023229622419456

noncomputable def p20903 :=
nat_lit
  726160092760845011641108680352084730665635051574293088600406698025494463278517871428368796037873571953229069519606366578500129568595417965255774940142501908736270114252581995678483000263073696052585636615852595813764117653360213026725315526893299630161439858650147191471010804971783800565158779952697821

noncomputable def p20904 :=
nat_lit
  44942328371557897693232629769725618340449424473557664318357520289433168951375240783177119330601884005280028469967848339414697442203604155623211857659868531094441973356216371319075554900311523529863270738021251442209537670585615720368478277635206809290837627671146574559986811484619929076208839082406056034304

noncomputable def p20905 :=
@p20900 p20901 p20902 p20903
  p20904 19012918537349 18014398509481984 1 18014398509481984
  p20891 p20892 p20898

noncomputable def p20906 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p20907 :=
p20906
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p20908 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p20907
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p20909 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p20908
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p20826 (Enclosure.sfrac false 1 16)))))

noncomputable def p20910 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  (Enclosure.sfrac false 3 1)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p20911 :=
p20909
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p20910
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 4 1) Real.pi))
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p20826 (Enclosure.sfrac false 1 16)))))

noncomputable def p20912 :=
@Neg.neg Real Real.instNeg
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
          (Enclosure.sfrac false 12 1)))))

noncomputable def p20913 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20911
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 3 1) p20912)
    (@iteratedDeriv Real c11 Real
      Real.normedAddCommGroup
      c9
      (@OfNat.ofNat Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
        (Enclosure.sfrac false 12 1))))

noncomputable def p20914 :=
@Neg.neg Real Real.instNeg
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 4 1)
      c12)
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
          (Enclosure.sfrac false 12 1)))))

noncomputable def p20915 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20913
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 3 1) p20914)
    (@iteratedDeriv Real c11 Real
      Real.normedAddCommGroup
      c9
      (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
        (Enclosure.sfrac false 12 1))))

noncomputable def p20916 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 8 1)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      c12 Real.pi))
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
        (Enclosure.sfrac false 12 1))))

noncomputable def p20917 :=
@Enclosure.Real.IsNear.of_eq
  (@iteratedDeriv Real c11 Real
    Real.normedAddCommGroup
    c8
    (@OfNat.ofNat Nat 3 (instOfNatNat 3)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
      (Enclosure.sfrac false 12 1)))
  (p20825
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20915
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p20916
        (Zeta.RiemannSiegel.correction
          (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
            (Enclosure.sfrac false 12 1))))))

noncomputable def p20918 :=
@Enclosure.Real.IsNear.recentre'
  (p20825
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20915
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p20916
        (Zeta.RiemannSiegel.correction
          (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
            (Enclosure.sfrac false 12 1))))))

noncomputable def p20919 :=
nat_lit
  6540668646338132808718459488266190446667750928721614481355077698860029562606703759088946848694662843957136211696879718100989060272891958533762669908954245030508981030196657583549312541963029674162807595082820121634953530136547042435800035047847190369292316873952056873748773552870277777897434963129868102619926884461537

noncomputable def p20920 :=
@p20829
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20915
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p20916
      (Zeta.RiemannSiegel.correction
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
          (Enclosure.sfrac false 12 1)))))
  400408428432373195

noncomputable def p20921 :=
nat_lit
  55578631829543777931927902584542973843422429648039587057495587851083993296508428875921913167897549520688505524719931891538036162311288259293864274842827662346399963761184514063616236995567496092619504031582085273654793496161834232464584275551188750506299377684655

noncomputable def p20922 :=
nat_lit
  125955231460491477573475786427621032361709434041052227527609040505093074454480376118282617542185112928074454067529947442741953744769736656487116570106253523089501067161322852174933318537813768637901361681988522625958449433505907473287200188342818373796829838966784

noncomputable def p20923 :=
nat_lit
  65339956836644827499421978101030349902129748056674941992102471475294336859886131773970516071286366699376699967780268185020013004619728783045819661552341715358834948059043230133589471601055547932122966479966386510851495398059055672139112652206234240528607756492699935819623882633013193378546864237356373

noncomputable def p20924 :=
nat_lit
  89884656743115795386465259539451236680898848947115328636715040578866337902750481566354238661203768010560056939935696678829394884407208311246423715319737062188883946712432742638151109800623047059726541476042502884419075341171231440736956555270413618581675255342293149119973622969239858152417678164812112068608

noncomputable def p20925 :=
@p20920 18014398509481984 129961 18014398509481984
  p20921 p20922 p20923 p20924
  p20901 p20902 p20919 p20899

noncomputable def p20926 :=
@p20832 (@Neg.neg Real Real.instNeg p20833) true
  400408428432373195 18014398509481984 129961 18014398509481984
  (BSN.inv_eq_neg_inv_neg
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
          (Enclosure.sfrac false 12 1)))))

noncomputable def p20927 :=
nat_lit 32112092083513587453132800000000

noncomputable def p20928 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
      (Enclosure.sfrac false 12 1)))
  (@HDiv.hDiv Real Real Real c4
    c60
    c41)
  false

noncomputable def p20929 :=
nat_lit 62916208229841650323422136557304974676920574479857895077786811614969

noncomputable def p20930 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
      (Enclosure.sfrac false 12 1)))
  false p20929

noncomputable def p20931 :=
nat_lit 17121160916665483071190193476420586781586741707238487049875990517021925826300145246347493

noncomputable def p20932 :=
nat_lit 1197262141301475670592458614961179049702139939205939200000000000000000000000000000000000000000000000000

noncomputable def p20933 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
    (Enclosure.sfrac false 12 1))
  p20538 p20539 1

noncomputable def p20934 :=
@Enclosure.Real.IsNear.subLit_ff_p p20583 (Enclosure.sfrac false 12 1)
  229554547319513285 18014398509481984 41 18014398509481984 12
  1 0

noncomputable def p20935 :=
@p20805
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 102026300 100000)
    (@Inv.inv Real Real.instInv
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)))
  false 2925176223193363359527

noncomputable def p20936 :=
@p20935 18014398509481984000 1020263 18014398509481984000
  (BSN.t_div_two_pi_mk
    (@OfScientific.ofScientific Real c2 102026300
      true 5)
    102026300 100000
    (Enclosure.sfrac_ofScientific_eq 102026300 5 100000 (Eq.refl true)))

noncomputable def p20937 :=
@p20808 1 2867080569611329 18014398509481984 1
  18014398509481984 2925176223193363359527 18014398509481984000 1020263
  18014398509481984000 (Enclosure.Real.IsNear.const false 102026300 100000)
  d264

noncomputable def p20938 :=
@p20804 2925176223193363359527 18014398509481984000 1020263
  18014398509481984000 114777273659756622 114777273659756663 9007199254740992
  (p20936 (p20937 (Eq.refl true))) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p20939 :=
@Enclosure.Real.IsNear.recentre' p20583 false 229554547319513285
  18014398509481984 41 18014398509481984 229554547319513285
  18014398509481984 41 18014398509481984
  (p20938 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p20940 :=
@p20933 p20541 13381765205729477 18014398509481984 41
  18014398509481984 p20929 p16711 p20931
  p20932 d263
  (@p20934 1 13381765205729477 13381765205729477
    18014398509481984 41 18014398509481984
    (p20939 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p20941 :=
@p20928 42040055262383233 9007199254740992 129
  9007199254740992 true 810468837853737 18014398509481984 1
  3565158400000000
  (@p20930 p16711 p20931 p20932
    42040055262383233 9007199254740992 129 9007199254740992
    (p20940 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div 42040055262383233 9007199254740992)

noncomputable def p20942 :=
nat_lit 164540984275960878853431576005981584595301471965117791900304297426944

noncomputable def p20943 :=
nat_lit 107839786668602559178668060348078522694548577690162289924414440996864

noncomputable def p20944 :=
BSN.cos_reduce2
  (@HDiv.hDiv Real Real Real c4
    c60
    c41)
  (@HDiv.hDiv Real Real Real c4
    (@Nat.cast Real Real.instNatCast p20942)
    (@Nat.cast Real Real.instNatCast p20943))
  p2138 p2102 false

noncomputable def p20945 :=
BSN.sin_reduce_arg_pos_rat_q2 42040055262383233 9007199254740992 p2138
  p2102 0 p20942 p20943 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p20946 :=
nat_lit
  12030604761270535359710988179875969252271005875499663668293839044514043898642081595381589172792764053142207194122547779671245836529459871926378125176719334068543462260697904572477624337991138636343102404020372828509375199330477307095522821024553074434359413066721318854473834488880157143687524769658934941017331304030487130069300152216664849683055763577281242194873695810810315387240811278256439602304032643681

noncomputable def p20947 :=
nat_lit
  53102990615883956733387301248634318761034095274990519830731939129350906266306940335926087483461735510804137932871510655900434920930053303934669231053358814434699611628336331660878506027009877679359193392996227855949211921999426701532324897040027625005419272233679190997940926390958862794299232502772129059116465853813021764814338443329201266457768197681217975241444878096295327802569303860828984006294896640000

noncomputable def p20948 :=
nat_lit
  102069451295303957549070300658578153487578897237966582831581671641185939210357543571128878472337269690547280652721215712645156829310122968959767695083495517752953962718919747480111124510390453982190421036357010488170029888653609143280170029323784047878411542264812404055289742547829914840366738738338027164914945423416748886426820000376926989937665057764568164809594437218995495807037459984751201

noncomputable def p20949 :=
nat_lit
  184873905279892884182265935497443288845915848169285711905336851481480816156338079982535269058560827485884498878503275129184913466326589506671298756708923740258294104497862754769167062628038004664305977898037148538049788881014428036240651195454851218839849143634312229656083234683517633485435956449987215596983535096326936802278357297216057508142928207244018110296339322720851061261531647042032519509597716683361

noncomputable def p20950 :=
nat_lit
  12266790832269194005412466588434527633798876008522810080899077938880059347516903217598926208679660902995755862493318961513000466734842313208908592373325886134415610286145692613662934892239281743931973673782128634724267953981867568053967051216246381376251851885979893120524353996311497305483122708140361812655903612230808027672112180409045492551744453664361352280773766840244220722393509191851495305454121123840000

noncomputable def p20951 :=
BSN.cos_dyadic_bound_f 56291755025487756889 36893488147419103232 6 5
  18014398509481984 7137280000000001 p20946 p20947
  p20948 p20949 p20950

noncomputable def p20952 :=
@BSN.binarySplit_of_base5 (BSN.cosEvenP 56291755025487756889) (BSN.cosEvenQ 36893488147419103232)
  0 5 p20946 p20947 p20948
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p20953 :=
p20951 p20948 810468837853737 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p20952 (Eq.refl true))

noncomputable def p20954 :=
@BSN.binarySplit_of_base5 (BSN.cosOddP 56291755025487756889) (BSN.cosOddQ 36893488147419103232)
  0 5 p20949 p20950 p20948
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p20955 :=
@BSN.cos_arg_round false 810468837853737 18014398509481984 p20942
  p20943 56291755025487756889 36893488147419103232 7137280000000001
  7130316800000000
  (p20953 (p20954 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p20956 :=
p20944 810468837853737 18014398509481984 0 p2139
  7130316800000000 3565158400000000 p20945 d102
  p20955 (Eq.refl true) (Eq.refl true)

noncomputable def p20957 :=
@p20836 810468837853737 18014398509481984 873417841
  59813432551014400000000
  (@p20837 810468837853737 18014398509481984 468912632854740992
    p20927 810468837853737 18014398509481984 873417841
    59813432551014400000000
    (p20941 (p20956 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p20958 :=
@p20835 810468837853737 18014398509481984 873417841
  59813432551014400000000 200204214216121617 200204214216251578 9007199254740992
  p20957 (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p20959 :=
@Enclosure.Real.IsNear.recentre' p20833 false 400408428432373195
  18014398509481984 129961 18014398509481984 400408428432373195
  18014398509481984 129961 18014398509481984
  (p20958 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p20960 :=
nat_lit
  15441741453146664552307299863370358508985443024490954900963658593918002189466004329145978022326082528870222554572381195790368294489844586591939345145079510116468745931911510910554103459890421220768127544981743616880378745110126666453264537145687682585000589627330735

noncomputable def p20961 :=
@Enclosure.Real.IsNear.subLit_tt_n p20915
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p20916
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
        (Enclosure.sfrac false 12 1))))
  p20960 p20922

noncomputable def p20962 :=
nat_lit
  65318477724485141052584774879944335281450054350283811647210499897516448842999444236741616460847865129712778831039169158042629151913108121622231298804774369262336964807888803488545814716702137805188748227578434572175574873380551988090007988900475293693775896015890661888603463680079253924203877513233755

noncomputable def p20963 :=
nat_lit
  18700844981389752023229993008722328607966555473126169878227521895222978053564606238015518475458058116716532197360493829845828040286519646927120865782161562345167620438280552361350492403724045091219691965

noncomputable def p20964 :=
nat_lit
  153090103458041951154620325043801237641319743206933311288544235956760011447392195175450369025277569052617268428910122535686807015741471080782585043071649294869136754165183653769539196448293593632735232

noncomputable def p20965 :=
nat_lit
  10739556079843223418601610543007310339846853195565172445985788888944008443343768614449805219250784831960568370549513488691926353310330711794181373783673048248991625577213322521828442176705063467109126193975969337960262339251842024552331652879473417415930238404636965510209476466969727171493362061309

noncomputable def p20966 :=
nat_lit
  8508538496841280372316487198066468170885636495889636635940166189416170205108614435209105699339577940956218530349583768731632809040802283090069914608459180718634562004310195578138870922162252615836943959006137989158203813345115756981518079692342722771373776674452781771752442677403671358543970755266820328299639488453844825216344898499796383085732122944070397638928073988345374134495978250193823768619113670417639487666483698475334743547609320691465116170804264960

noncomputable def p20967 :=
@p20961 p20962 p20924 p20963
  p20964 p20965 p20904 p20966
  p20921 p20922 p20923 p20924

noncomputable def p20968 :=
@Enclosure.Real.IsNear.subLit_tf p20913
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 3 1) p20914)
    (@iteratedDeriv Real c11 Real
      Real.normedAddCommGroup
      c9
      (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
        (Enclosure.sfrac false 12 1))))

noncomputable def p20969 :=
nat_lit
  14794153713568487832856623765215811292206598851128416586400151698618146268762197980742492026975248503766842065141419656580308643653518427013142710621868196484691299213005339990247632363593249100261669013069164742045320534261780046120809873637734442393536612136489135

noncomputable def p20970 :=
nat_lit
  65252270968456241312519804428147809866884410464276379796379769702431887162312787710481084420983932845065826555957814609541228283720314906945858012976767684152540871295953074688989837148683709530582698396697707749074569882546225510832488635196043390729611560323895507144766033329121724566193098932202093

noncomputable def p20971 :=
nat_lit
  255428325226834670321232297969041390745312592867260368950788233452486563417210627530054287842801000717970547730270136028170470854569576248228124102361352790231143853420292772638548694307280871517918989024192354745330397289642225573925

noncomputable def p20972 :=
nat_lit
  49680578953622685924767343630800081768220352547734291556449665216833630485964060362588109082516687294415607382308194342597490561411674060526217192801317796454542559232667196977608489140211150234408415974198927000028571099322113851392

noncomputable def p20973 :=
nat_lit
  33103378014449870032485225898262707282821943003715925415365097542280840343328263130266019931966142323476137540677274250700434096396607338186642914003342554898046755967864399777988784009214137303024915440363411550502495417163238628759676852215951482082167845997577371918715175478764679005389290515831

noncomputable def p20974 :=
nat_lit
  767154655444481173636280064657222418239129415509910017435199541463991379336838507350701805864473557144675200754097959864505173589866216083335140827622242171081709456834537954126070936933091733323293071573519360999607154213795460097745631134337411257450778639552919541587490261063176258689524433728488945230080669323188866473260154169442578739671554727126546989343752747251677007208824301592643133173684333951710979885639101057385634762207959822057812403650806481583244924475585870878154035424133120

noncomputable def p20975 :=
@p20968 p20969 p20922 p20970
  p20924 p20971 p20972 p20973
  p20904 p20974 p20960 p20922

noncomputable def p20976 :=
@Enclosure.Real.IsNear.subLit_tf p20911
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 3 1) p20912)
    (@iteratedDeriv Real c11 Real
      Real.normedAddCommGroup
      c9
      (@OfNat.ofNat Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
        (Enclosure.sfrac false 12 1))))

noncomputable def p20977 :=
nat_lit
  71312864249196691113820128673791647133475936803398248486913353359604759106338294493375906162389741831325115196084754226284020287288736853277266521368487465512927607581467970645900958704983101781424610371435864378223395

noncomputable def p20978 :=
nat_lit
  2757826131550993649364364103715456897804056554542556176448634698108099443712107910064330000971904293916892446775667965408323532095584366159791555750475533307061324308088589961496711008293655788792731796366049346060288

noncomputable def p20979 :=
nat_lit
  33524700798590392350307777243009194871034816289549660533555878022574172041202958964213647910944091933527136078786598913654477942255696080585873686561170628933884181527967424113776108573797129195721800991958316022957454777158247731324858109603835435236796635691428199084406977414384682241952057247

noncomputable def p20980 :=
nat_lit
  5617791046444737211654078721215702292556178059194708039794690036179146118921905097897139916325235500660003558745981042426837180275450519452901482207483566386805246669527046414884444362538940441232908842252656430276192208823201965046059784704400851161354703458893321819998351435577491134526104885300757004288

noncomputable def p20981 :=
nat_lit
  11537157842851069867751814876124514107925439047515802158153439024834463854244903225070164594944488822105569065985280647968051015483022211803282815962191187459550055357139661800650158347703811528657474189877729179531176585419455313359288018271516890483341938406297775

noncomputable def p20982 :=
nat_lit
  65251734573243463866242199503711921719766473907215747001811232808383525975560128463137657002617357739594890121780554023958609812073238815808568638997782705422477929149048627210204016730946528776515566847881836416018202563269790978868787437466289729362647771577724444293580682817483094411277227699286141

noncomputable def p20983 :=
nat_lit
  40799703705461349747504017876658626778059905108668882471855214401360597341704426595855113105728575383165490193049510552495637971296244465146244250434693357160740910020223207398720403462542084152334482318365190898567449845414253202371725584856111803989298839478375859160988347184701339319486374273220873082346396691655165044014561749885538496499959451999496962180979194942471478762448834136537684966813187402798930938171184247154023812929651316342697044278294685675505875340366970880

noncomputable def p20984 :=
@p20976 p20977 p20978 p20979
  p20980 p20981 p20922 p20982
  p20924 p20983 p20969 p20922

noncomputable def p20985 :=
nat_lit
  1652895363702474642697084450924790784264761098026281518338026363408579700813134670477320707397750919916511957196734857702329228742295908347325955989497243703845622812430703995044735947163638647028856767893169971291112624923700493748075581266390689367465792086454929362831293171043982157674425707414578307385073888831573670574216170997250364902653434765796626692161114500269

noncomputable def p20986 :=
nat_lit
  276978483140055660679575521154310658598553426872826080593424264214176807023660163124123274254828011726923049202224793480793868237276543994954010579940377664898144237780470377568655909939538265926807969022980227546033961457550130800932105433260772020185747203501713259671584768000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p20987 :=
@Enclosure.Real.IsNear.subLit_tt_n
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p20908
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p20826 (Enclosure.sfrac false 1 16)))))

noncomputable def p20988 :=
@p20987
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p20910
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 4 1) Real.pi))
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p20826 (Enclosure.sfrac false 1 16)))))

noncomputable def p20989 :=
nat_lit
  78349322346963895616111781004019437775617455450824903977980576910362442685458720083368370170751078899826685892491132581453082061463321729956066170676410421194442001897935143424608792525259545875372750031904376715651875

noncomputable def p20990 :=
nat_lit
  163402807900044491592393400960026147705431621216073940750962985361243940218671131005919655127296469597865885647274020025893622820890199059854481898406114799153927628099111458843610032549056423954407297281148060893023860082347060231845196154803742356275904124887321924461526373996947585575650157853

noncomputable def p20991 :=
nat_lit
  57952917254616549379383067086612972089165041393902826863456709708380474910960322165888213340140679405869769600498350356083845783343555

noncomputable def p20992 :=
nat_lit
  22713710134237715329666368996500141698551292521478689383796568724394977753543685103943470334805111423773828800195818060422956300894208

noncomputable def p20993 :=
nat_lit
  72611094036948804790050392474917776783727647820390390224082536985233615770652761957224900773895877778244222967310131666113370940340713320526382440702416664199022303183637723765755317241238505065111

noncomputable def p20994 :=
nat_lit
  17498005798264095394980017816940970922825355447145699491406164851279623993595007385788105416184430592000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p20995 :=
nat_lit
  1619779727398497345345694815312206473952886569336676490474078820334431296174277492789361770405950327752300079816893004176789567668564707652653363268925337694560898339760369675367373154553603432326411587885096865517313694308688713605875317786431099273534260439108818468912456046455245670092426426108863743509506981955182671151088331249789136560885596160

noncomputable def p20996 :=
@p20988 p20989 p20978 p20990
  p20924 p20991 p20992 p20993
  p20994 p20995 p20977 p20978

noncomputable def p20997 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p20908
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p20826 (Enclosure.sfrac false 1 16)))))

noncomputable def p20998 :=
nat_lit
  1372149773876354535845846466277713015312225349149451829764190912691811538673819741558046282990048660627892449564575842500293174022913744264461445613475334529254455804506272164841679445464963508628994671314093118877019177354375412898301600033778565571453805351131295904139454480916948618612034287315851087372469521273

noncomputable def p20999 :=
nat_lit
  754792484964308270448310916197653778183384244083288085675241260049124832478429770417225345035531753508293675006152768979954116925984958526512286850286539208729879065395200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p21000 :=
nat_lit
  8700662281771230972564772267323438625056990720799338936870374691749703877743639200892827896972200636246729205647986188423558679434193721893639275569745107872152802157857871122153266877049260527833203625

noncomputable def p21001 :=
@Enclosure.Real.IsNear.mulLit_ft p20908
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p20826 (Enclosure.sfrac false 1 16))))
  p21000

noncomputable def p21002 :=
nat_lit
  306180206916083902309240650087602475282639486413866622577088471913520022894784390350900738050555138105234536857820245071373614031482942161565170086143298589738273508330367307539078392896587187265470464

noncomputable def p21003 :=
nat_lit
  171404849551976995571377555541380127258734309910185991540973067339744721316702823850208824338488430877973358739200661710604089912798039164881917653933083344499075172634730563113849547795012194258789308622474318558127429231404752197579948847856294511765937346362150627825125066641070492562600551

noncomputable def p21004 :=
nat_lit
  214524926879081553593184399971293538039669853129478294043576983099548224481176751628829988770670454843040509730983776813660062124991145119142938384097345536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p21005 :=
@p21001 p21002 p21003 p21004
  9004983736825835 9007199254740992 4290195057 119626865102028800000000
  p20989 p20978 p20998 p20999

noncomputable def p21006 :=
@Enclosure.Real.IsNear.mulLit_ff p20907
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p21007 :=
nat_lit
  423027117289093836221384169001817950678307842285482179982909038142275279395241009360165066341036600887912725973661419347728826042687025

noncomputable def p21008 :=
nat_lit
  45427420268475430659332737993000283397102585042957378767593137448789955507087370207886940669610222847547657600391636120845912601788416

noncomputable def p21009 :=
nat_lit
  62552911054842051188193615989538947139225415633783598250643199593537627648997037333456164410763992962606638757877829924901714189247782996337244929266692377822560926945051674226543792576592451

noncomputable def p21010 :=
nat_lit
  358359158748448673689190764890951084499463279557543925583998256154206699388825751260940398923457138524160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p21011 :=
nat_lit 20567623034495109985035012459197539093155726957210738362907623671545

noncomputable def p21012 :=
nat_lit 6739986666787659948666753771754907668409286105635143120275902562304

noncomputable def p21013 :=
nat_lit 17121160916665483071190193476420586769614120294223730343951404367410135329278745854288101

noncomputable def p21014 :=
nat_lit 598631070650737835296229307480589524851069969602969600000000000000000000000000000000000000000000000000

noncomputable def p21015 :=
@p21006 p21007 p21008 p21009
  p21010 p21011 p21012 p21013
  p21014 p21000 p21002 p21003

noncomputable def p21016 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p21017 :=
@p21016
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p21018 :=
@p21017 p21011 p21012 p21013
  p21014 p21011 p21012 p21013
  p21014 p21007 p21008 p21009

noncomputable def p21019 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
        (Enclosure.sfrac false 12 1)))
    (Enclosure.sfrac false 1 1))
  p20538

noncomputable def p21020 :=
@p21019 p20539 1 p20541 4374565950988485
  9007199254740992 41 9007199254740992 p21011 p21012
  p21013 p21014

noncomputable def p21021 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
      (Enclosure.sfrac false 12 1)))
  (Enclosure.sfrac false 1 1) 13381765205729477 9007199254740992

noncomputable def p21022 :=
@p21021 41 9007199254740992 1 1 0 1
  4374565950988485 4374565950988485 9007199254740992 41
  9007199254740992

noncomputable def p21023 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 2 1)
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
    (Enclosure.sfrac false 12 1))
  2 1 0 1

noncomputable def p21024 :=
@p21023 13381765205729477 18014398509481984 41
  18014398509481984 13381765205729477 9007199254740992 41
  9007199254740992 (Enclosure.Real.IsNear.const false 2 1)
  (@p20934 1 13381765205729477 13381765205729477
    18014398509481984 41 18014398509481984
    (p20939 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p21025 :=
@p21018 p21010
  (p21020 d263
    (p21022 (p21024 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (p21020 d263
    (p21022 (p21024 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))

noncomputable def p21026 :=
@p21015 p21004 (p21025 (Eq.refl true))
  (p21020 d263
    (p21022 (p21024 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p21027 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p20826 (Enclosure.sfrac false 1 16))))
  true

noncomputable def p21028 :=
nat_lit 64224184167027174906265600000000

noncomputable def p21029 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p20826 (Enclosure.sfrac false 1 16)))
  (@HDiv.hDiv Real Real Real c4
    (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 14348257532550621))
    c41)
  true

noncomputable def p21030 :=
nat_lit 386828257844107186123297470342237432445612966906861133175694952646144274520119886435

noncomputable def p21031 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p20826 (Enclosure.sfrac false 1 16)))
  true p21030

noncomputable def p21032 :=
nat_lit 766650126570439697257420752883054207310710287475244825387227503163921722033901283700500323970371728581919

noncomputable def p21033 :=
nat_lit
  21567957333720511835733612069615704538909715538032457984882888199372800000000000000000000000000000000000000000000000000

noncomputable def p21034 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (p20826 (Enclosure.sfrac false 1 16)) p20538
  p20539 1

noncomputable def p21035 :=
nat_lit 82275220758710563972587653834855

noncomputable def p21036 :=
nat_lit 324518553658426726783156020576256

noncomputable def p21037 :=
nat_lit 61992811155058893548640402548839

noncomputable def p21038 :=
@p20867 (Enclosure.sfrac false 1 16) p21037
  p21036 1835895085758580139 p21036 1 16 0

noncomputable def p21039 :=
nat_lit 1316403532139369023561402461357680

noncomputable def p21040 :=
nat_lit 179071640021272071898427706693529

noncomputable def p21041 :=
@Enclosure.Real.IsNear.subLit_ff_n
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
      (Enclosure.sfrac false 12 1))
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
      (Enclosure.sfrac false 12 1)))
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
    (Enclosure.sfrac false 12 1))
  p21040

noncomputable def p21042 :=
nat_lit 1116763204870291042841577292401112977063150616576

noncomputable def p21043 :=
@p21041 p21036 1097304746869818795 p21036
  13381765205729477 18014398509481984 41 18014398509481984
  p21042 p21037 p21036 1835895085758580139

noncomputable def p21044 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
    (Enclosure.sfrac false 12 1))
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
    (Enclosure.sfrac false 12 1))
  13381765205729477 18014398509481984 41

noncomputable def p21045 :=
@p21044 18014398509481984 13381765205729477 18014398509481984
  41 18014398509481984 p21040 p21036
  1097304746869818795 p21036
  (@p20934 1 13381765205729477 13381765205729477
    18014398509481984 41 18014398509481984
    (p20939 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p21046 :=
p21045
  (@p20934 1 13381765205729477 13381765205729477
    18014398509481984 41 18014398509481984
    (p20939 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p21047 :=
@p21043 p21036 (p21046 (Eq.refl true))
  (@p20934 1 13381765205729477 13381765205729477
    18014398509481984 41 18014398509481984
    (p20939 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p21048 :=
@p21034 p20541 p21035 p21036
  1835895085758580139 p21036 p21030 p15946
  p21032 p21033 d263
  (@p21038 1 p21039 p21035 p21036
    1835895085758580139 p21036
    (p21047 (Eq.refl true) (Eq.refl true))
    (Enclosure.Real.IsNear.const false 1 16) (Eq.refl true)
    (Eq.refl true))

noncomputable def p21049 :=
@p21029 14348257532550621 9007199254740992 641
  18014398509481984 true 9004983736825835 9007199254740992 1
  3565158400000000
  (@p21031 p15946 p21032 p21033
    14348257532550621 9007199254740992 641 18014398509481984
    (p21048 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_true_div 14348257532550621 9007199254740992)

noncomputable def p21050 :=
nat_lit
  33940621270736513606170166545492707425016729280699412334605557006004578209058250985810926733809194147016023900071911813489041877399093336490109752006917254672179568162819020130477283351034469614794817446660929603637598573718284345849762176094669667122240758133209966720421944046202614906604136787315645826409249024268514849433574760263441

noncomputable def p21051 :=
nat_lit
  631159779000701449485347259390063050840833625402925001709384631724727185671284397617025828089119105944169806921029659564694922697933623422498326733281427003411066528366799609399086589178520758154920885272671818889120035322556203997044937997148430438378423017591466560577094107036676955467030630655367057903838605838758410796720917053440000

noncomputable def p21052 :=
nat_lit
  136767611309137818022566393027402754903119374508396607213274483530774733401616125745459204291003913155828212771542942137238422191772011771813289367646038365274474022967494689486256275266363773996217156085852680878241251200784797390248261242002751437218988731563891991727147550008698298533516376890743958159455886156249968401

noncomputable def p21053 :=
nat_lit
  408366297466676015090549663048137210807173689195905104546221810977116726128457456038729583897683462756632144918716166121133847543836293672481448661681544534330105160892554717721140533142398202014560259883909767858450284699610544092038490685320450377126894829752458045154869335727463388797010431352812139629173195750144524142035876723568401

noncomputable def p21054 :=
nat_lit
  53227808029059155573264285541895317287576969075646675144158103942118659324944984199035844835515711267958320383673501289955938480859068908630692221173400343954333277225600100392656302354055250604398327991328656726315789645535573203750789771092850966969913674483547013275334936360093089911052916518602621883223722425735292643856797338173440000

noncomputable def p21055 :=
BSN.sin_dyadic_bound_f 14348257532550621 9007199254740992 6 5
  9007199254740992 3565158400000000 p21050 p21051
  p21052 p21053 p21054

noncomputable def p21056 :=
@BSN.binarySplit_of_base5 (BSN.sinEvenP 14348257532550621) (BSN.sinEvenQ 9007199254740992)
  0 5 p21050 p21051 p21052
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p21057 :=
p21055 p21052 9004983736825835 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p21056 (Eq.refl true))

noncomputable def p21058 :=
@BSN.binarySplit_of_base5 (BSN.sinOddP 14348257532550621) (BSN.sinOddQ 9007199254740992) 0
  5 p21053 p21054 p21052 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p21059 :=
p21049
  (BSN.sin_neg_of_bound 14348257532550621 9007199254740992 false 9004983736825835
    9007199254740992 1 3565158400000000
    (p21057 (p21058 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p21060 :=
p21005 p21026
  (@p21027 9004983736825835 9007199254740992 2303280932909481984
    p21028 9004983736825835 9007199254740992 4290195057
    119626865102028800000000 (p21059 (Eq.refl true))
    (Eq.refl true))

noncomputable def p21061 :=
@p20997 true p20989 p20978 p20998
  p20999 p20989 p20978 p20990
  p20924 (p21060 (Eq.refl true)) (Eq.refl true)

noncomputable def p21062 :=
nat_lit
  290104519187901954710432298615480281269505263950989155646889630023113525640715430221718935790736898232985061082723423095

noncomputable def p21063 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p20910
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 4 1) Real.pi))
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p20826 (Enclosure.sfrac false 1 16))))
  p21062

noncomputable def p21064 :=
nat_lit
  21448840326903925211259895611218148854194331375632244038640256647094227491465652601531899651873211282338923694286797697583773434202647883926043608658480887865672732061164992403

noncomputable def p21065 :=
nat_lit
  19892929456391465686215289925872833604018246031893908697618559075726379880501335021322240000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p21066 :=
@p21063 p20387 p21064 p21065
  199765647970069 9007199254740992 4290195057 119626865102028800000000
  p20991 p20992 p20993 p20994

noncomputable def p21067 :=
nat_lit 61702869103485329955105037377592617279467180871632215088722871014635

noncomputable def p21068 :=
nat_lit 51363482749996449213570580429261760308842360882671191031854213102230405987836237562864303

noncomputable def p21069 :=
@Enclosure.Real.IsNear.mulLit_ff p20910
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 4 1) Real.pi)
  p21067 p21012 p21068 p21014

noncomputable def p21070 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 3 1)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p21071 :=
@p21070 3 1 0 1 p21011
  p21012 p21013 p21014 p21067
  p21012 p21068

noncomputable def p21072 :=
@p21071 p21014 (Enclosure.Real.IsNear.const false 3 1)
  (p21020 d263
    (p21022 (p21024 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p21073 :=
@p21069 p20538 p2930 1 p20548
  p21062 p20387 p21064 p21065
  p21072 d265 (Eq.refl true)

noncomputable def p21074 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p20826 (Enclosure.sfrac false 1 16)))
  (@HDiv.hDiv Real Real Real c4
    (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 14348257532550621))
    c41)
  true

noncomputable def p21075 :=
@p21074 14348257532550621 9007199254740992 641
  18014398509481984 true 199765647970069 9007199254740992 1
  3565158400000000
  (@p21031 p15946 p21032 p21033
    14348257532550621 9007199254740992 641 18014398509481984
    (p21048 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_true_div 14348257532550621 9007199254740992)

noncomputable def p21076 :=
nat_lit
  8094847621003180786558440892475124574155751891518981773900092181547321905666664428158300574816601308610682748049534051756924586731033420442516111668988983213407592231261665287045180376233802389751290006111791277652818151743654767971078133244696204889183578711831781473291817576659577134666129661994460569443045788234427698193204924395281

noncomputable def p21077 :=
nat_lit
  30055227571461973785016536161431573849563505971567857224256411034510818365299257029382182289958052664008086043858555217366424890377791591547539368251496523971955548969847600447575551865643845626424804060603419947100954062978866857002139904626115735160877286551974598122718767001746521688906220507398431328754219325655162418891472240640000

noncomputable def p21078 :=
nat_lit
  124343112994443726283116828477914612769906663691165685848309032844973155160025347162102992193731961858546138819480819676520845799024196016102734636469334344191636355569893197089009618565773001256710313452212761036153320336896376554921343735214540760357829614919280165133151188703154345132149390242962854719994840982863236095680596907929361

noncomputable def p21079 :=
nat_lit
  6942757569007715944338819853290693559249169879432175018803230948971999042384128373787284108980310165385867876131326255211644149677269857647481594066095697037521731812034795703389952480963728339704129737999390007780320388548118243967494317968632734822162653193506132166348035177403446510137336937209037636942224664226342518763930087587840000

noncomputable def p21080 :=
BSN.cos_dyadic_bound_t 14348257532550621 9007199254740992 6 5
  9007199254740992 3565158400000000 p21076 p21077
  p21052 p21078 p21079

noncomputable def p21081 :=
@BSN.binarySplit_of_base5 (BSN.cosEvenP 14348257532550621) (BSN.cosEvenQ 9007199254740992)
  0 5 p21076 p21077 p21052
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p21082 :=
p21080 p21052 199765647970069 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p21081 (Eq.refl true))

noncomputable def p21083 :=
@BSN.binarySplit_of_base5 (BSN.cosOddP 14348257532550621) (BSN.cosOddQ 9007199254740992) 0
  5 p21078 p21079 p21052 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p21084 :=
p21075
  (BSN.cos_neg_of_bound 14348257532550621 9007199254740992 true 199765647970069
    9007199254740992 1 3565158400000000
    (p21082 (p21083 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p21085 :=
p21066 p21073
  (@p20861 199765647970069 9007199254740992 2303280932909481984
    p21028 199765647970069 9007199254740992 4290195057
    119626865102028800000000 (p21084 (Eq.refl true))
    (Eq.refl true))

noncomputable def p21086 :=
@Enclosure.Real.IsNear.recentre' p20911 true p20977 p20978
  p20985 p20986 p20977 p20978
  p20979 p20980
  (@p20996 p20985 p20986 p21061
    (p21085 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p21087 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 3 1) p20912)
    (@iteratedDeriv Real c11 Real
      Real.normedAddCommGroup
      c9
      (@OfNat.ofNat Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
        (Enclosure.sfrac false 12 1))))

noncomputable def p21088 :=
nat_lit
  249166227791856297058563839802687244868351040759205409617825355557910461940545011709201965599297522803207988520529115486250191845439419662900807533379026286418960526528904405132241878565012059555972142195665548573111048616493741164325296335434184378373720261054844065335904065390373950690787577367949710350290954669815781325029661508625524272236453080497627200033631350161603239817735664879

noncomputable def p21089 :=
nat_lit
  343227977057204456014277121881274395527679633337183049936840561957190295514880068237309017794094113308538159798310047595007106250755938658165857982390324797241492372059624079129348397439262904429074752873612653363200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p21090 :=
nat_lit 31729278365164974481804370046778007922640644997411501224085193201241

noncomputable def p21091 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 3 1) p20912)
  (@iteratedDeriv Real c11 Real
    Real.normedAddCommGroup
    c8
    (@OfNat.ofNat Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
      (Enclosure.sfrac false 12 1)))
  p21090

noncomputable def p21092 :=
nat_lit 1684996666696914987166688442938726917102321526408785780068975640576

noncomputable def p21093 :=
nat_lit 1094189809993722961702023518527869753837601152485069037353142591096927778034811197257084120675623

noncomputable def p21094 :=
nat_lit 3975284453540055937514022744988289813464136516894720000000000000000000000000000000000000000000000000000000000

noncomputable def p21095 :=
nat_lit
  363612361745910860925913783716914295610792191630728965882988895351516811915924532515238534114149465331865077911218803197372928670039047931946867037476818851704196153503732328454403946699900988296775

noncomputable def p21096 :=
nat_lit
  6657160275015770563029744017466903385545101379333121898503371420865235499304555624746556764110277823736666192602065058968623387997404782197208845805462991133240657192053039244659562254668851703291424903837471987910608437988970379834696890002067857872897351422004429612126998608871

noncomputable def p21097 :=
nat_lit
  172680964629615029912095122564540850567397046423572784518937594751890297139367343022480053834596998290449698702675688732346267274458152299782022149090551172033413120000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p21098 :=
@p21091 p21092 p21093 p21094
  p21095 p18275 p21096 p21097
  p20981 p20922 p21088 p21089

noncomputable def p21099 :=
nat_lit 10576426121721658160601456682259335974213548332470500408028397733747

noncomputable def p21100 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 3 1) p20912
  3 1 0 1 p21099 p21092

noncomputable def p21101 :=
nat_lit 364729936664574320567341172842623251279200384161689679117714197032309259344937065752361373558541

noncomputable def p21102 :=
@Enclosure.Real.IsNear.neg
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
          (Enclosure.sfrac false 12 1)))))

noncomputable def p21103 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
        (Enclosure.sfrac false 12 1))))
  p20538

noncomputable def p21104 :=
@p21103 p20539 1 p20541 2249519719300151
  2251799813685248 873417841 59813432551014400000000 p21099
  p21092 p21101 p21094

noncomputable def p21105 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
        (Enclosure.sfrac false 12 1))))
  true

noncomputable def p21106 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
      (Enclosure.sfrac false 12 1)))
  (@HDiv.hDiv Real Real Real c4
    c60
    c41)
  false

noncomputable def p21107 :=
@p21106 42040055262383233 9007199254740992 129
  9007199254740992 true 17996157754401208 18014398509481984 1
  3565158400000000
  (@p20930 p16711 p20931 p20932
    42040055262383233 9007199254740992 129 9007199254740992
    (p20940 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div 42040055262383233 9007199254740992)

noncomputable def p21108 :=
BSN.sin_reduce2
  (@HDiv.hDiv Real Real Real c4
    c60
    c41)
  (@HDiv.hDiv Real Real Real c4
    (@Nat.cast Real Real.instNatCast p20942)
    (@Nat.cast Real Real.instNatCast p20943))
  p2138 p2102 false

noncomputable def p21109 :=
nat_lit
  50456279644036877965665955352351949893764370238007533355752284105021605625053643897276462065834474082177697104735891752279955639232787053479786023745395141585510480899759599658236351726069663488643997569748625314619089465406049774594715121379378082422367612523566204799911084125528338032541197765878950240790875963133490571532970147648026197434742609603697675738835387358561216367874327132717808685806150163041

noncomputable def p21110 :=
nat_lit
  1115162802933563091401133326221320693981716000774800916445370721716369031592445747054447837152696445726886896590301723773909133339531119382628053852120535103128691844195062964878448626567207431266543061252920784974933450361987960732178822837840580125113804716907263010956759454210136118680283882558214710241445782930073457061101107309913226595613132151305577480070342440022201883853955381077408664132192829440000

noncomputable def p21111 :=
nat_lit
  607205476145513235573713416089139815109870204227476099846041894232368331152647397375768123628571821495181704160408011018296806739433991162729600737795620422885365705575424469762386484591829568443499577979098014924161900420147655570282541228969911704575089833456755830992371848532596062424848650905542759769769920094745123990964347233219104719066834955014902576507957739977872406582825278873785336575951276808801

noncomputable def p21112 :=
nat_lit
  94045396380730487374828910511331378525791382732008210620226264198080454997629591334925100933210733589634128279115445371599670244967124401268299208195498460363853012193783643371415834173834493370145131498996319532886054313860984688413747392657888923884597531125845847257353380638388146008703940762409440563695261027102861545486193383136015442896707478093437034152598879108539025538350237137528130675148261949440000

noncomputable def p21113 :=
BSN.sin_dyadic_bound_f 56291755025487756889 36893488147419103232 6 5
  18014398509481984 7137280000000001 p21109 p21110
  p20948 p21111 p21112

noncomputable def p21114 :=
@BSN.binarySplit_of_base5 (BSN.sinEvenP 56291755025487756889) (BSN.sinEvenQ 36893488147419103232)
  0 5 p21109 p21110 p20948
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p21115 :=
p21113 p20948 17996157754401208 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p21114 (Eq.refl true))

noncomputable def p21116 :=
@BSN.binarySplit_of_base5 (BSN.sinOddP 56291755025487756889) (BSN.sinOddQ 36893488147419103232)
  0 5 p21111 p21112 p20948
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p21117 :=
@BSN.sin_arg_round false 17996157754401208 18014398509481984 p20942
  p20943 56291755025487756889 36893488147419103232 7137280000000001
  7130316800000000
  (p21115 (p21116 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p21118 :=
p21108 17996157754401208 18014398509481984 0 p2139
  7130316800000000 3565158400000000 p20945 d102
  p21117 (Eq.refl true) (Eq.refl true)

noncomputable def p21119 :=
p21104 d263
  (@p21105 17996157754401208 18014398509481984 468912632854740992
    p20927 2249519719300151 2251799813685248 873417841
    59813432551014400000000
    (p21107 (p21118 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p21120 :=
@Neg.neg Real Real.instNeg
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p20907
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p20826 (Enclosure.sfrac false 1 16)))))

noncomputable def p21121 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p21120
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 4 1) Real.pi)
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p20826 (Enclosure.sfrac false 1 16)))))

noncomputable def p21122 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p21121
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) p20912)
    (@iteratedDeriv Real c11 Real
      Real.normedAddCommGroup
      c9
      (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
        (Enclosure.sfrac false 12 1))))

noncomputable def p21123 :=
@Enclosure.Real.IsNear.of_eq
  (@iteratedDeriv Real c11 Real
    Real.normedAddCommGroup
    c8
    (@OfNat.ofNat Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
      (Enclosure.sfrac false 12 1)))
  (p20825
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p21122
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p20914
        (Zeta.RiemannSiegel.correction
          (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
            (Enclosure.sfrac false 12 1))))))

noncomputable def p21124 :=
@p20829
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p21122
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p20914
      (Zeta.RiemannSiegel.correction
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
          (Enclosure.sfrac false 12 1)))))
  400408428432373195

noncomputable def p21125 :=
nat_lit
  908103665972962930435547719959415505502232932979593608894718711745315370565373063179577295061977994919876984277708116818798586636297942675987885526558114818931849996087799276755445

noncomputable def p21126 :=
nat_lit
  4149515568880992958512407863691161151012446232242436899995657329690652811412908146399707048947103794288197886611300789182395151075411775307886874834113963687061181803401509523685376

noncomputable def p21127 :=
nat_lit
  33250487107565098997637309102205767292084915598338027357947441880680108360000198529235969292174847601823041898430107892002986077687049991816561163104789979258227916556500202667693329653427050086521406160571120849581775601744552353419426590505660332477071141673657

noncomputable def p21128 :=
nat_lit
  19171438284628087290972233987467282575178578343641254080213797678299314191026885614563829855438670067885287140749338422856669880640429182137254543360000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p21129 :=
@p21124 18014398509481984 129961 18014398509481984
  p21125 p21126 p21127 p21128
  p21095 p18275 p21096 p21097

noncomputable def p21130 :=
nat_lit
  2725086861610776072513042053034057833007957586869724599902017945778998312227207130320579287006150887701574932583936158461228210698799855048223090539347516345878629625535144728077835

noncomputable def p21131 :=
@Enclosure.Real.IsNear.subLit_ff_n p21122
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p20914
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
        (Enclosure.sfrac false 12 1))))
  p21130 p21126

noncomputable def p21132 :=
nat_lit
  33212447382759323906272681499952616342332931871882251191912311477887883425748748187831540791549221609658804551201880688134513746242874861528758729887523769464205450929625264863155310749691986906047917066886716441550511491729658070533361894861909663412469541673657

noncomputable def p21133 :=
nat_lit
  1433040984215056905527947482904503056421357477246558202339538972582079492016122803057294840084337966887470723492057560407010271715623259292382932711015

noncomputable def p21134 :=
nat_lit
  1636695303948070935006594848413799576108321023021532394741645684048066898202337277441635046162952078575443342063780035504608628272942696526664263794688

noncomputable def p21135 :=
nat_lit
  1129714889210048604500611161824781149578686637649486576907774090795282872262744047153365603195963443084331436380313417198082164097041063336059649685593637875971349724318828918682825214558531841888724274548563250882930821347

noncomputable def p21136 :=
nat_lit
  569358989537900224617432129447075219483402232458225704351852839691350679598134693334936147383087031009655774459933491200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p21137 :=
nat_lit
  1486289005595976044918880153689411767257797934970235610727085809256782702206091250895710001415526205131386649432885113226358501129801771340532639088520273214958875596098486543734421197100845753387908960409333986517392469698698353634314959742919317610485359811857578756661121868843596894664948434862154927388990055080503808266076160

noncomputable def p21138 :=
@p21131 p21132 p21128 p21133
  p21134 p21135 p21136 p21137
  p21125 p21126 p21127 p21128

noncomputable def p21139 :=
@Enclosure.Real.IsNear.subLit_ff_p p21121
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) p20912)
    (@iteratedDeriv Real c11 Real
      Real.normedAddCommGroup
      c9
      (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
        (Enclosure.sfrac false 12 1))))

noncomputable def p21140 :=
nat_lit
  5225071483561320275759307110846137146550205727043995166410768613556933207882747101165280330272077934748733310002229537499294362401157207486985563511045

noncomputable def p21141 :=
nat_lit
  409173825987017733751648712103449894027080255755383098685411421012016724550584319360408761540738019643860835515945008876152157068235674131666065948672

noncomputable def p21142 :=
nat_lit
  16901338078762930028909089549769332332383229118312564749088421861582847553727602360038169529104163401874331272856781604840428444488029644190588068072513158609651123681964102133512806617671155610602063709549269787041

noncomputable def p21143 :=
nat_lit
  21434691370838596691479797814478125909963378163133202987363871611909672643694482572609360842657394108598805626726907904000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p21144 :=
nat_lit
  50263433157364525702120096684227647898274432639960878798873347190608397562040534768160223368951726908484329295776686239787069087831640608960579102184834021760074109845014265506945525

noncomputable def p21145 :=
nat_lit
  33197330628601367429955982322829358182755814463657797557940795801429491345475239943158160389669532008881689551868507470230563823091542141318903861226350950045307061223235346382957769937769610967335316204659985497846546580054864995018604013396504223412469541673657

noncomputable def p21146 :=
nat_lit
  1115034217312235965232099736588036706195488960875811720410670143817335796073996355420915326550631582050706350482572894404662588311604978701017472034331132351795479522700496178757712683833977987202664310635887097238858274304510890934415727565820741916785274468983097264404252522171405567777044133916967612040145352970367644330885120

noncomputable def p21147 :=
@p21139 p21140 p21141 p21142
  p21143 p21144 p21126 p21145
  p21128 p21146 p21130 p21126

noncomputable def p21148 :=
@Enclosure.Real.IsNear.subLit_ft p21120
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 4 1) Real.pi)
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p20826 (Enclosure.sfrac false 1 16)))))

noncomputable def p21149 :=
nat_lit
  84506286194166208877990812365647426532890792575888716649291685800479886962134926963428481213421064967437694570398788567481126320199777718033534654725

noncomputable def p21150 :=
nat_lit
  425963302774438040102855295198037969650627859524324254819940556846907832308622025470742357902655398060818764569431827246275626435430147302130904330945594323500563604821417772559576859863009153564827277032309987473

noncomputable def p21151 :=
nat_lit
  1260864198284623334792929283204595641762551656654894293374345388935863096687910739565256520156317300505812095689818112000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p21152 :=
nat_lit 42338168633380015846805810477218374337175029926169764842080533029495

noncomputable def p21153 :=
nat_lit 3369993333393829974333376885877453834204643052817571560137951281152

noncomputable def p21154 :=
nat_lit 1791539510604386448647252369741786521795350061838610201786039401527296071651648260885877479538957

noncomputable def p21155 :=
nat_lit
  17608456066107858194247600727535695589664588404368185676488420088406670404912658529338456949667580881415198474579256554605521807295265464659965847265420691962374435955829423714099440112959167106732482733077321052323840

noncomputable def p21156 :=
@p21148 p21149 p21141 p21150
  p21151 p21152 p21153 p21154
  p21094 p21155 p21140 p21141

noncomputable def p21157 :=
@Enclosure.Real.IsNear.neg
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p20907
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p20826 (Enclosure.sfrac false 1 16)))))

noncomputable def p21158 :=
@Enclosure.Real.IsNear.mulLit_ft p20907
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p20826 (Enclosure.sfrac false 1 16))))
  p21007

noncomputable def p21159 :=
@p21158 p21008 p21009 p21010
  199765647970069 9007199254740992 4290195057 119626865102028800000000
  p21149 p21141 p21150 p21151

noncomputable def p21160 :=
p21159 (p21025 (Eq.refl true))
  (@p20861 199765647970069 9007199254740992 2303280932909481984
    p21028 199765647970069 9007199254740992 4290195057
    119626865102028800000000 (p21084 (Eq.refl true))
    (Eq.refl true))

noncomputable def p21161 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 4 1) Real.pi)
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p20826 (Enclosure.sfrac false 1 16))))
  p20538

noncomputable def p21162 :=
@p21161 p2930 1 p20548 9004983736825835
  9007199254740992 4290195057 119626865102028800000000 p21152
  p21153 p21154 p21094

noncomputable def p21163 :=
p21162 d265
  (@p21027 9004983736825835 9007199254740992 2303280932909481984
    p21028 9004983736825835 9007199254740992 4290195057
    119626865102028800000000 (p21059 (Eq.refl true))
    (Eq.refl true))

noncomputable def p21164 :=
@p21147 p21132 p21128
  (@p21156 p21142 p21143
    (@p21157 true p21149 p21141 p21150
      p21151 (p21160 (Eq.refl true)))
    (p21163 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p21165 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1) p20912)
  (@iteratedDeriv Real c11 Real
    Real.normedAddCommGroup
    c8
    (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
      (Enclosure.sfrac false 12 1)))
  p21099

noncomputable def p21166 :=
nat_lit 1987642226770027968757011372494144906732068258447360000000000000000000000000000000000000000000000000000000000

noncomputable def p21167 :=
nat_lit
  4752402425818912947055768431047781268570241794448909568167738803827432478206757304881684405102735667676829130403575

noncomputable def p21168 :=
nat_lit
  4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100828498788352

noncomputable def p21169 :=
nat_lit
  2660606487174508122225779763975567473598973807991680332394310863592232829286361216632651287121258773423422431136591597848508641916263145493947010719580279

noncomputable def p21170 :=
nat_lit
  19290632918160719181630039783843767535005675217533520328584219520644421898456409967394876347645952000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p21171 :=
@p21165 p7486 p21101 p21166
  p21167 p21168 p21169 p21170
  p21144 p21126 p21145 p21128

noncomputable def p21172 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 2 1) p20912
  2 1 0 1 p21099 p21092

noncomputable def p21173 :=
@Neg.neg Real Real.instNeg
  (p20906
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p20826 (Enclosure.sfrac false 1 16)))))

noncomputable def p21174 :=
@Enclosure.Real.IsNear.of_eq
  (@iteratedDeriv Real c11 Real
    Real.normedAddCommGroup
    c8
    (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
      (Enclosure.sfrac false 12 1)))
  (p20825
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p21173
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p20912
        (Zeta.RiemannSiegel.correction
          (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
            (Enclosure.sfrac false 12 1))))))

noncomputable def p21175 :=
@p20829
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p21173
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p20912
      (Zeta.RiemannSiegel.correction
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
          (Enclosure.sfrac false 12 1)))))
  400408428432373195

noncomputable def p21176 :=
nat_lit 11868887087179704209616777054405122681269860974008501942995742491141209010502580052705322456327685

noncomputable def p21177 :=
nat_lit 273406340597876490546562778389702670669146178861651554553221325801244124899921990402939147127881728

noncomputable def p21178 :=
nat_lit
  13259286512825016357530624966459029173032253262492983141350865602933053183571219200781692923866762964097480811628344763858543695267256893

noncomputable def p21179 :=
nat_lit
  2141690482533400350554368938720691543654081636375687872473807473810361245820256256000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p21180 :=
@p21175 18014398509481984 129961 18014398509481984
  p21176 p21177 p21178 p21179
  p21167 p21168 p21169 p21170

noncomputable def p21181 :=
nat_lit 185211110930792895355463759740122592659332909861935726654242546948603148386910365075

noncomputable def p21182 :=
@Enclosure.Real.IsNear.subLit_ff_n p21173
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p20912
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
        (Enclosure.sfrac false 12 1))))
  p21181 p18030

noncomputable def p21183 :=
nat_lit 145365511217101637006880421449081916184984040177289619464867694201459910784900038746301524236514406251861874649

noncomputable def p21184 :=
nat_lit
  1053122916685571866979180276836704323188950954005491112543109775360000000000000000000000000000000000000000000000000000000000

noncomputable def p21185 :=
nat_lit 845985577259974186302148442389656749044790951986959067773224173878890582931087423951665892100154885

noncomputable def p21186 :=
nat_lit
  12963662966010469935360360334714468698641362935697522224145747903532594034246392904157180080906398403741905813620506990098349544867256893

noncomputable def p21187 :=
nat_lit
  720541179050114257400657285376731107919427310947486294294303773440661395180766769554561204836521405199151667982098779220252879297366033648698156864943710066227842430469893343150080

noncomputable def p21188 :=
@p21182 p21183 p21184 p21185
  p21177 p21186 p21179 p21187
  p21176 p21177 p21178 p21179

noncomputable def p21189 :=
@Enclosure.Real.IsNear.neg
  (p20906
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p20826 (Enclosure.sfrac false 1 16)))))

noncomputable def p21190 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p21191 :=
@p21190
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p20826 (Enclosure.sfrac false 1 16))))
  p21011

noncomputable def p21192 :=
@p21191 p21012 p21013 p21014
  9004983736825835 9007199254740992 4290195057 119626865102028800000000
  p21181 p18030 p21183 p21184

noncomputable def p21193 :=
p21192
  (p21020 d263
    (p21022 (p21024 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (@p21027 9004983736825835 9007199254740992 2303280932909481984
    p21028 9004983736825835 9007199254740992 4290195057
    119626865102028800000000 (p21059 (Eq.refl true))
    (Eq.refl true))

noncomputable def p21194 :=
@Enclosure.Real.IsNear.mulLit_ff p20912
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
      (Enclosure.sfrac false 12 1)))
  p21099 p21092 p21101

noncomputable def p21195 :=
nat_lit 79987849158470030805595997900455

noncomputable def p21196 :=
nat_lit 1031317332326306779571628071

noncomputable def p21197 :=
nat_lit 1077503010193994991272197724569600000000

noncomputable def p21198 :=
@p20829
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p20826 (Enclosure.sfrac false 1 16))))
  400408428432373195

noncomputable def p21199 :=
@p21198 18014398509481984 129961 18014398509481984
  199765647970069 9007199254740992 4290195057 119626865102028800000000
  p21195 p18612 p21196 p21197

noncomputable def p21200 :=
p21199
  (p20926
    (@Enclosure.Real.IsNear.neg p20833 false 400408428432373195
      18014398509481984 129961 18014398509481984
      (p20959 (Eq.refl true))))
  (@p20861 199765647970069 9007199254740992 2303280932909481984
    p21028 199765647970069 9007199254740992 4290195057
    119626865102028800000000 (p21084 (Eq.refl true))
    (Eq.refl true))

noncomputable def p21201 :=
@p21194 p21094 p21195 p18612
  p21196 p21197 p21185 p21177
  p21186 p21179
  (@p21102 true p21099 p21092 p21101
    p21094 (p21119 (Eq.refl true)))
  (@p20827 false p21195 p18612 p21196
    p21197
    (BSN.correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
        (Enclosure.sfrac false 12 1))
      (p20828 (Eq.refl true) (Eq.refl true)
        (p20586 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p21200 (Eq.refl true)))

noncomputable def p21202 :=
p21180
  (p20926
    (@Enclosure.Real.IsNear.neg p20833 false 400408428432373195
      18014398509481984 129961 18014398509481984
      (p20959 (Eq.refl true))))
  (p21188
    (@p21189 true p21181 p18030 p21183
      p21184 (p21193 (Eq.refl true)))
    (p21201 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p21203 :=
p21171
  (@p21172 p21101 p21094 p21099
    p7486 p21101 p21166
    (Enclosure.Real.IsNear.const false 2 1)
    (@p21102 true p21099 p21092 p21101
      p21094 (p21119 (Eq.refl true)))
    (Eq.refl true))
  (@p21174 false p21167 p21168 p21169
    p21170
    (BSN.deriv_correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
        (Enclosure.sfrac false 12 1))
      (p20828 (Eq.refl true) (Eq.refl true)
        (p20586 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p21202 (Eq.refl true)))

noncomputable def p21204 :=
nat_lit
  17915733443162724314353097614414018834932334220554731556125937356895966082253963163379918941804582223255162599157191233

noncomputable def p21205 :=
nat_lit
  10086913586276986678343434265636765134100413253239154346994763111486904773503285916522052161250538404046496765518544896

noncomputable def p21206 :=
nat_lit
  152307315530716752621496641582402690568207377958488510745172030761843956680818917112854588826078690688358948210605422887549507629761660755164442963180605667533594136046481585072589241

noncomputable def p21207 :=
@Enclosure.Real.IsNear.mulLit_ff p20914
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
      (Enclosure.sfrac false 12 1)))
  p21204 p21205 p21206

noncomputable def p21208 :=
nat_lit
  264202969342699153645046819327998571303367330111090974890246487724490982787908355751936000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p21209 :=
@Enclosure.Real.IsNear.neg
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 4 1)
      c12)
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
          (Enclosure.sfrac false 12 1)))))

noncomputable def p21210 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 4 1)
    c12)
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
        (Enclosure.sfrac false 12 1))))
  p20550

noncomputable def p21211 :=
@p21210 p20555 p20551 p20557
  810468837853737 18014398509481984 873417841 59813432551014400000000
  p21204 p21205 p21206 p21208

noncomputable def p21212 :=
p21211 d267
  (@p20837 810468837853737 18014398509481984 468912632854740992
    p20927 810468837853737 18014398509481984 873417841
    59813432551014400000000
    (p20941 (p20956 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p21213 :=
@p21207 p21208 p21195 p18612
  p21196 p21197 p21133 p21134
  p21135 p21136
  (@p21209 true p21204 p21205 p21206
    p21208 (p21212 (Eq.refl true)))
  (@p20827 false p21195 p18612 p21196
    p21197
    (BSN.correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
        (Enclosure.sfrac false 12 1))
      (p20828 (Eq.refl true) (Eq.refl true)
        (p20586 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p21200 (Eq.refl true)))

noncomputable def p21214 :=
p21129
  (p20926
    (@Enclosure.Real.IsNear.neg p20833 false 400408428432373195
      18014398509481984 129961 18014398509481984
      (p20959 (Eq.refl true))))
  (p21138
    (p21164 (p21203 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true))
    (p21213 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p21215 :=
p21098
  (@p21100 p21101 p21094 p21090
    p21092 p21093 p21094
    (Enclosure.Real.IsNear.const false 3 1)
    (@p21102 true p21099 p21092 p21101
      p21094 (p21119 (Eq.refl true)))
    (Eq.refl true))
  (@p21123 false p21095 p18275 p21096
    p21097
    (BSN.iteratedDeriv_two_correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
        (Enclosure.sfrac false 12 1))
      (p20828 (Eq.refl true) (Eq.refl true)
        (p20586 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p21214 (Eq.refl true)))

noncomputable def p21216 :=
@p21087 false p20981 p20922 p21088
  p21089 p20981 p20922 p20982
  p20924 (p21215 (Eq.refl true)) (Eq.refl true)

noncomputable def p21217 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 3 1) p20914)
    (@iteratedDeriv Real c11 Real
      Real.normedAddCommGroup
      c9
      (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
        (Enclosure.sfrac false 12 1))))

noncomputable def p21218 :=
nat_lit
  7508114924695357967072410912252905148674646691012960072294644271167554444896648124115988642728999948507222848829729791971635924322439983987072948749889485164671440533224007339145221870107543298167452553158833283686497169070427663094363825268203625468686701591856260777547368819878294886568055568860249846902556291033511366908443465718351592502928809

noncomputable def p21219 :=
nat_lit
  10193284994956159202585729917157337367462074169503546244839332230385088631235808861630880365738560470668958108460660388626553688616749026043824108030000951797265793100055808144933126144000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p21220 :=
nat_lit
  53747200329488172943059292843242056504797002661664194668377812070687898246761889490139756825413746669765487797471573699

noncomputable def p21221 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 3 1) p20914)
  (@iteratedDeriv Real c11 Real
    Real.normedAddCommGroup
    c8
    (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
      (Enclosure.sfrac false 12 1)))
  p21220

noncomputable def p21222 :=
nat_lit
  456921946592150257864489924747208071704622133875465532235516092285531870042456751338563766478236072065076844631816268662648522889284982265493328889541817002600782408139444755217767723

noncomputable def p21223 :=
@p21221 p21205 p21222 p21208
  p21167 p21168 p21169 p21170
  p20971 p20972 p21218 p21219

noncomputable def p21224 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 3 1) p20914
  3 1 0 1 p21204 p21205

noncomputable def p21225 :=
p21223
  (@p21224 p21206 p21208 p21220
    p21205 p21222 p21208
    (Enclosure.Real.IsNear.const false 3 1)
    (@p21209 true p21204 p21205 p21206
      p21208 (p21212 (Eq.refl true)))
    (Eq.refl true))
  (@p21174 false p21167 p21168 p21169
    p21170
    (BSN.deriv_correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
        (Enclosure.sfrac false 12 1))
      (p20828 (Eq.refl true) (Eq.refl true)
        (p20586 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p21202 (Eq.refl true)))

noncomputable def p21226 :=
@p21217 false p20971 p20972 p21218
  p21219 p20971 p20972 p20973
  p20904 (p21225 (Eq.refl true)) (Eq.refl true)

noncomputable def p21227 :=
@p20975 p20962 p20924
  (@p20984 p20970 p20924
    (p21086 (Eq.refl true)) p21216 (Eq.refl true)
    (Eq.refl true))
  p21226 (Eq.refl true) (Eq.refl true)

noncomputable def p21228 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p20916
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
        (Enclosure.sfrac false 12 1))))
  true p20963

noncomputable def p21229 :=
nat_lit
  2260614122030539159943260236291233295497200575396196588245945766356857012584403710714136431656641069207674883835566761002024053505717015188442899269304014016097134513118732221867001778711755868879512468562349557632420062717584017378643904111022158279368572093922760409670389005603260909334904874589050516069093

noncomputable def p21230 :=
nat_lit
  9460098856819850004338118223831761549906095513064457241606712053797826671609509463612650566821863014166062517128648605216637871417608785924119444733296640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p21231 :=
nat_lit
  233796072505213650777150292897775976129034757095593663065764637151747517630190696304951166048310605363335311415093205124886928440342796061331741946997094677557704896259323

noncomputable def p21232 :=
nat_lit
  943490606205385338060388645247067222729230305104110107094051575061406040598037213021531681294414691885367093757690961224942646157481198158140358562858174010912348831744

noncomputable def p21233 :=
nat_lit
  63601903853335253720822538499430938325196322982954155884361241718045112450768997866725229684282999300461505692725750395745521852503061164830399279587396056207989035309512362600102506955920604610576906685214360236710562808337372781564706816453634303148745255783873509941

noncomputable def p21234 :=
@Enclosure.Real.IsNear.mulLit_tf p20916
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
      (Enclosure.sfrac false 12 1)))
  p21231 p21232 p21233

noncomputable def p21235 :=
nat_lit
  17559299170990978409660250369620480745441999391238719887248483624476403829714520123481588402304937253764141569414682954956800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p21236 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 8 1)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      c12 Real.pi))
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
        (Enclosure.sfrac false 12 1))))

noncomputable def p21237 :=
@p21236 p20559 p13788 p20560
  p20561 2249519719300151 2251799813685248 873417841
  59813432551014400000000 p21231 p21232 p21233

noncomputable def p21238 :=
@p21237 p21235 d268
  (@p21105 17996157754401208 18014398509481984 468912632854740992
    p20927 2249519719300151 2251799813685248 873417841
    59813432551014400000000
    (p21107 (p21118 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p21239 :=
@p21234 p21235 p21195 p18612
  p21196 p21197 p20963 p20964
  p21229 p21230 (p21238 (Eq.refl true))
  (@p20827 false p21195 p18612 p21196
    p21197
    (BSN.correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
        (Enclosure.sfrac false 12 1))
      (p20828 (Eq.refl true) (Eq.refl true)
        (p20586 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p21200 (Eq.refl true)))

noncomputable def p21240 :=
p20967 p21227
  (@p21228 p20964 p21229 p21230
    p20963 p20964 p20965 p20904
    (p21239 (Eq.refl true)) (Eq.refl true))
  (Eq.refl true)

noncomputable def p21241 :=
p20925
  (p20926
    (@Enclosure.Real.IsNear.neg p20833 false 400408428432373195
      18014398509481984 129961 18014398509481984
      (p20959 (Eq.refl true))))
  (p21240 (Eq.refl true)) (Eq.refl true)

noncomputable def p21242 :=
@p20918 false p20901 p20902 p20919
  p20899 p20901 p20902 p20903
  p20904 p21241 (Eq.refl true)

noncomputable def p21243 :=
@p20905 p20899
  (@p20917 false p20901 p20902 p20903
    p20904
    (BSN.iteratedDeriv_three_correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
        (Enclosure.sfrac false 12 1))
      (p20828 (Eq.refl true) (Eq.refl true)
        (p20586 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    p21242)

noncomputable def p21244 :=
@Enclosure.Real.IsNear.recentre' p20896 false p20891 p20892
  p20898 p20899 p20891 p20892
  p20894 p20895
  (p21243 d269 (Eq.refl true))

noncomputable def p21245 :=
@p20893 p20894 p20895 1348198123 17179869184
  1 17179869184 p20820 p20794 p20889
  p20890
  (@p20897 p20892 p20894 p20895
    (BSN.correctionLinear_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p20583
        (Enclosure.sfrac false 12 1)))
    (@Enclosure.Real.IsNear.neg p20896 false p20891 p20892
      p20894 p20895 (p21244 (Eq.refl true))))

noncomputable def p21246 :=
@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv p20583) false
  1348198123 17179869184 1 17179869184 1348198123
  17179869184

noncomputable def p21247 :=
@Enclosure.Real.IsNear.inv_image p20583 218920276021 17179869184 41
  17179869184 674099061 674099062 8589934592
  (p20811 (Eq.refl true)) (Eq.refl true) (Eq.refl true)

noncomputable def p21248 :=
@p20888 p20820 p20794 p20889
  p20890 p20820 p20794 p20821
  p20822
  (p21245
    (@p21246 1 17179869184
      (p21247 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (Eq.refl true))
    (Eq.refl true))

noncomputable def p21249 :=
@p20815 false p20793 p20794 p20816
  p20817 p20793 p20794 p20795
  p20578
  (p20887 (p21248 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p21250 :=
@p20796 p20791
  (@p20798 17179869184
    (@p2563 1 0 1
      (BSN.neg_one_pow_even_mk 12 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1))
    p20814 (Eq.refl true))
  p21249 (Eq.refl true)

noncomputable def p21251 :=
@Enclosure.Real.IsNear.recentre' p20584 false p20788 p20789
  p20790 p20791 p20592 p20588
  p20593 p20588 p21250

noncomputable def p21252 :=
@p20585 p20575 p20577 p20578
  (BSN.hardyZApproximantRS_eq
    (@OfScientific.ofScientific Real c2 102026300
      true 5)
    12
    (p20586 (Eq.refl true) (Eq.refl true)
      (Eq.refl true)))
  (p20590
    (p20787 (p21251 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))

theorem d270 : p20576 p20577 p20578 :=
@p20579 p20575 p20577 p20578
  (@Eq.refl Real
    (hardyZApproximantRS
      (@OfScientific.ofScientific Real c2 102026300
        true 5)))
  p21252

noncomputable def p21253 :=
Enclosure.Real.IsNear
  (hardyZErrorBoundRS
    (@OfScientific.ofScientific Real c2 101903100
      true 5))
  false 5936636289 549755813888

noncomputable def p21254 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Real.sqrt p19939)
  (@HDiv.hDiv Real Real Real c4
    (@OfScientific.ofScientific Real c2 101903100
      true 5)
    c7)

noncomputable def p21255 :=
@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 25 4) (@Inv.inv Real Real.instInv p21254))
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 1 32)
    (@Inv.inv Real Real.instInv
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p21254
          p21254)
        p21254)))

noncomputable def p21256 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZErrorBoundRS
    (@OfScientific.ofScientific Real c2 101903100
      true 5))
  p21255 false 5936636289

noncomputable def p21257 :=
BSN.hardyZErrorBoundRS_mk
  (@OfScientific.ofScientific Real c2 101903100
    true 5)
  101903100 100000
  (Enclosure.sfrac_ofScientific_eq 101903100 5 100000 (Eq.refl true))
  (Eq.refl true)

noncomputable def p21258 :=
@Enclosure.Real.IsNear.addLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 25 4) (@Inv.inv Real Real.instInv p21254))
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 1 32)
    (@Inv.inv Real Real.instInv
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p21254
          p21254)
        p21254)))

noncomputable def p21259 :=
@p21258 742079525 68719476736 25 68719476736 89
  549755813888 1 549755813888 407962539352028872704 5936636289
  549755813888

noncomputable def p21260 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 25 4)
  (@Inv.inv Real Real.instInv p21254) 25 4 0 1
  29683181 17179869184

noncomputable def p21261 :=
@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv p21254) false 29683181
  17179869184 1 17179869184 29683181 17179869184

noncomputable def p21262 :=
nat_lit 170824089551446149770351673

noncomputable def p21263 :=
@Enclosure.Real.IsNear.mulLit_ff (Real.sqrt p19939)
  (@HDiv.hDiv Real Real Real c4
    (@OfScientific.ofScientific Real c2 101903100
      true 5)
    c7)

noncomputable def p21264 :=
@p21263 61308647361 17179869184 7 17179869184
  2786296826051193 17179869184000 1019031 17179869184000
  p21262 295147905179352825856000 81979490018418759

noncomputable def p21265 :=
@p21264 295147905179352825856000
  (p20135
    (p20144 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (p20139 (p20141 (Eq.refl true))) (Eq.refl true)

noncomputable def p21266 :=
@Enclosure.Real.IsNear.inv_image p21254 p21262 295147905179352825856000
  81979490018418759 295147905179352825856000 14841590 14841591
  8589934592 p21265 (Eq.refl true) (Eq.refl true)

noncomputable def p21267 :=
@p21259 201 549755813888
  (@p21260 1 17179869184 742079525 68719476736 25
    68719476736 (Enclosure.Real.IsNear.const false 25 4)
    (@p21261 1 17179869184
      (p21266 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (Eq.refl true))
    (Eq.refl true))

noncomputable def p21268 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 1 32)
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p21254
        p21254)
      p21254))
  1

noncomputable def p21269 :=
@p21268 32 0 1 89 17179869184 1
  17179869184 89 549755813888 1 549755813888

noncomputable def p21270 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p21254
        p21254)
      p21254))
  false

noncomputable def p21271 :=
nat_lit 4984795476799324243347268360840637633119407983986310352770176872122560048058217

noncomputable def p21272 :=
@Enclosure.Real.IsNear.inv_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p21254
      p21254)
    p21254)
  p21271 p5990

noncomputable def p21273 :=
nat_lit 7176698420637659044241346056997227719755262019235657022484576670003351

noncomputable def p21274 :=
nat_lit 29180869571080493638248623596246922496556254093898929

noncomputable def p21275 :=
nat_lit 5601628699059428099727824990682927260713539

noncomputable def p21276 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p21254
    p21254)
  p21254 p21274 p5994 p21275

noncomputable def p21277 :=
@Enclosure.Real.IsNear.mulLit_ff p21254 p21254 p21262
  295147905179352825856000 81979490018418759 295147905179352825856000
  p21262 295147905179352825856000 81979490018418759
  295147905179352825856000 p21274

noncomputable def p21278 :=
@p21276 p8228 p21262 295147905179352825856000
  81979490018418759 295147905179352825856000 p21271 p5990
  p21273 p5990
  (@p21277 p5994 p21275 p8228
    p21265 p21265 (Eq.refl true))
  p21265

noncomputable def p21279 :=
@p21272 p21273 p5990 44 45
  8589934592 (p21278 (Eq.refl true)) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p21280 :=
p21269 (Enclosure.Real.IsNear.const false 1 32)
  (@p21270 89 17179869184 1 17179869184 89
    17179869184 1 17179869184 (p21279 (Eq.refl true))
    (Eq.refl true))

theorem d271 : p21253 201 549755813888 :=
@p21256 549755813888 201 549755813888
  (p21257 (Eq.refl true))
  (p21267 (p21280 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p21281 :=
Enclosure.Real.IsNear
  (hardyZErrorBoundRS
    (@OfScientific.ofScientific Real c2 102026300
      true 5))
  false 5927676689 549755813888

noncomputable def p21282 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Real.sqrt p20583)
  (@HDiv.hDiv Real Real Real c4
    (@OfScientific.ofScientific Real c2 102026300
      true 5)
    c7)

noncomputable def p21283 :=
@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 25 4) (@Inv.inv Real Real.instInv p21282))
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 1 32)
    (@Inv.inv Real Real.instInv
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p21282
          p21282)
        p21282)))

noncomputable def p21284 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZErrorBoundRS
    (@OfScientific.ofScientific Real c2 102026300
      true 5))
  p21283 false 5927676689

noncomputable def p21285 :=
BSN.hardyZErrorBoundRS_mk
  (@OfScientific.ofScientific Real c2 102026300
    true 5)
  102026300 100000
  (Enclosure.sfrac_ofScientific_eq 102026300 5 100000 (Eq.refl true))
  (Eq.refl true)

noncomputable def p21286 :=
@Enclosure.Real.IsNear.addLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 25 4) (@Inv.inv Real Real.instInv p21282))
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 1 32)
    (@Inv.inv Real Real.instInv
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p21282
          p21282)
        p21282)))

noncomputable def p21287 :=
@p21286 740959575 68719476736 25 68719476736 89
  549755813888 1 549755813888 407346840328265007104 5927676689
  549755813888

noncomputable def p21288 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 25 4)
  (@Inv.inv Real Real.instInv p21282) 25 4 0 1
  29638383 17179869184

noncomputable def p21289 :=
@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv p21282) false 29638383
  17179869184 1 17179869184 29638383 17179869184

noncomputable def p21290 :=
nat_lit 171082284682181675758284553

noncomputable def p21291 :=
@Enclosure.Real.IsNear.mulLit_ff (Real.sqrt p20583)
  (@HDiv.hDiv Real Real Real c4
    (@OfScientific.ofScientific Real c2 102026300
      true 5)
    c7)

noncomputable def p21292 :=
@p21291 61327169377 17179869184 7 17179869184
  2789665435730089 17179869184000 1020263 17179869184000
  p21290 295147905179352825856000 16419499973467723

noncomputable def p21293 :=
@p21292 59029581035870565171200
  (p20803
    (p20812 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (p20807 (p20809 (Eq.refl true))) (Eq.refl true)

noncomputable def p21294 :=
@Enclosure.Real.IsNear.inv_image p21282 p21290 295147905179352825856000
  16419499973467723 59029581035870565171200 14819191 14819192
  8589934592 p21293 (Eq.refl true) (Eq.refl true)

noncomputable def p21295 :=
@p21287 201 549755813888
  (@p21288 1 17179869184 740959575 68719476736 25
    68719476736 (Enclosure.Real.IsNear.const false 25 4)
    (@p21289 1 17179869184
      (p21294 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (Eq.refl true))
    (Eq.refl true))

noncomputable def p21296 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 1 32)
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p21282
        p21282)
      p21282))
  1

noncomputable def p21297 :=
@p21296 32 0 1 89 17179869184 1
  17179869184 89 549755813888 1 549755813888

noncomputable def p21298 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p21282
        p21282)
      p21282))
  false

noncomputable def p21299 :=
nat_lit 5007432733136610563700947273428132389241969535369979977074906399578503688380377

noncomputable def p21300 :=
@Enclosure.Real.IsNear.inv_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p21282
      p21282)
    p21282)
  p21299 p5990

noncomputable def p21301 :=
nat_lit 1441754331625944358329336750708081137422160013383623436269010616603451

noncomputable def p21302 :=
nat_lit 29269148132075054848721345238699382559328013318409809

noncomputable def p21303 :=
nat_lit 5618171138947758813158836846385827003989283

noncomputable def p21304 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p21282
    p21282)
  p21282 p21302 p5994 p21303

noncomputable def p21305 :=
@Enclosure.Real.IsNear.mulLit_ff p21282 p21282 p21290
  295147905179352825856000 16419499973467723 59029581035870565171200
  p21290 295147905179352825856000 16419499973467723
  59029581035870565171200 p21302

noncomputable def p21306 :=
@p21304 p8228 p21290 295147905179352825856000
  16419499973467723 59029581035870565171200 p21299 p5990
  p21301 p16796
  (@p21305 p5994 p21303 p8228
    p21293 p21293 (Eq.refl true))
  p21293

noncomputable def p21307 :=
@p21300 p21301 p16796 44 45
  8589934592 (p21306 (Eq.refl true)) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p21308 :=
p21297 (Enclosure.Real.IsNear.const false 1 32)
  (@p21298 89 17179869184 1 17179869184 89
    17179869184 1 17179869184 (p21307 (Eq.refl true))
    (Eq.refl true))

theorem d272 : p21281 201 549755813888 :=
@p21284 549755813888 201 549755813888
  (p21285 (Eq.refl true))
  (p21295 (p21308 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p21309 :=
@LE.le Real Real.instLE
  c18
  (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE d57))

noncomputable def p21310 :=
@OfNat.ofNat Real 1019031
  (@instOfNatAtLeastTwo Real 1019031
    (@AddMonoidWithOne.toNatCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real
            (@DivisionSemiring.toSemiring Real
              c3)))))
    (Mathlib.Meta.NormNum.instAtLeastTwo 1019029))

noncomputable def p21311 :=
@LE.le Real Real.instLE
  c18
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            c3))))
    p21310 p6033)

noncomputable def p21312 :=
@congrArg Real Prop (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE d57))
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            c3))))
    p21310 p6033)

noncomputable def p21313 :=
p21312
  (@LE.le Real Real.instLE
    c17)

noncomputable def p21314 :=
@Mathlib.Meta.NormNum.IsNNRat.to_eq Real
  c3 1019031 1000
  (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE d57)) p21310
  p6033
  (@Mathlib.Meta.NormNum.isNNRat_ofScientific_of_true Real
    c3 101903100
    5 1019031 1000
    (p342
      (p343 p4
        (@p344 1019031 1000
          (p348 (@Eq.refl Nat (Nat.mul 101903100 1))
            (@Eq.refl Nat 100000))))))
  (@Eq.refl Real p21310)

noncomputable def p21315 :=
@congrArg Real Prop
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            c3))))
    p21310 p6033)

noncomputable def p21316 :=
@p21315
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            c3))))
    p21310 p6033)

noncomputable def p21317 :=
p21316
  (@LE.le Real Real.instLE
    c17)

noncomputable def p21318 :=
@Mathlib.Meta.NormNum.IsNNRat.to_eq Real
  c3 1019031 1000
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            c3))))
    p21310 p6033)

noncomputable def p21319 :=
@Mathlib.Meta.NormNum.isNNRat_mul Real
  (@DivisionSemiring.toSemiring Real
    c3)
  (@HMul.hMul Real Real Real
    c19)
  p21310
  (@Inv.inv Real
    (@InvOneClass.toInv Real
      (@DivInvOneMonoid.toInvOneClass Real
        (@DivisionMonoid.toDivInvOneMonoid Real
          (@GroupWithZero.toDivisionMonoid Real
            (@DivisionSemiring.toGroupWithZero Real
              c3)))))
    p6033)

noncomputable def p21320 :=
@p21319 1019031 1 1019031 1 1000 1000
  1
  (@Eq.refl (Real → Real → Real)
    (@HMul.hMul Real Real Real
      c19))
  (@Mathlib.Meta.NormNum.IsNat.to_isNNRat Real
    (@DivisionSemiring.toSemiring Real
      c3)
    p21310 1019031
    (@Mathlib.Meta.NormNum.isNat_ofNat Real
      c5
      p21310 1019031
      (@Eq.refl Real
        (@OfNat.ofNat Real 1019031
          (@instOfNatAtLeastTwo Real 1019031
            (@AddMonoidWithOne.toNatCast Real
              c5)
            (Mathlib.Meta.NormNum.instAtLeastTwo 1019029))))))

noncomputable def p21321 :=
@p21318 p21310 p6033
  (@Mathlib.Meta.NormNum.isNNRat_div Real
    c3 p21310
    p6033 1019031 1000
    (p21320 p6044 (@Eq.refl Nat (Nat.mul 1019031 1))
      (@Eq.refl Nat 1000)))
  (@Eq.refl Real p21310)

noncomputable def p21322 :=
@le_of_not_gt Real Real.linearOrder
  c18
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            c3))))
    p21310 p6033)

noncomputable def p21323 :=
@LT.lt Real
  (@Preorder.toLT Real (@PartialOrder.toPreorder Real (@LinearOrder.toPartialOrder Real Real.linearOrder)))
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            c3))))
    p21310 p6033)

noncomputable def p21324 :=
@HMul.hMul Real Real Real
  c19
  c15

noncomputable def p21325 :=
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
  p21310

noncomputable def p21326 :=
@HSub.hSub Real Real Real
  (@instHSub Real
    (@SubNegMonoid.toSub Real
      (@AddGroup.toSubNegMonoid Real
        (@AddGroupWithOne.toAddGroup Real
          (@Ring.toAddGroupWithOne Real
            c32)))))
  p21325
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real
          (@DivisionSemiring.toSemiring Real
            c3))))
    p3705 (p6050 Real.pi))

noncomputable def p21327 :=
@HAdd.hAdd Real Real Real
  c35
  (p21324
    c14)
  p21326

noncomputable def p21328 :=
@Eq.mp
  (@LT.lt Real c29
    (@HAdd.hAdd Real Real Real
      c35
      p21327 (p6053 p3713))
    (@OfNat.ofNat Real 0
      c49))
  (@LT.lt Real c29
    c25
    (@OfNat.ofNat Real 0
      c49))

noncomputable def p21329 :=
@Mathlib.Tactic.Ring.Common.add_congr Real Real.instCommSemiring p21327
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

noncomputable def p21330 :=
@p21329
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

noncomputable def p21331 :=
@Mathlib.Tactic.Ring.Common.add_congr Real Real.instCommSemiring
  (p21324
    c14)
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 918231))
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))

noncomputable def p21332 :=
@p21331 p21326
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      1019031)
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

noncomputable def p21333 :=
@Mathlib.Tactic.Ring.Common.mul_congr Real Real.instCommSemiring
  c15

noncomputable def p21334 :=
@p21333
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      918231)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@Neg.neg Real
    c36
    c23)

noncomputable def p21335 :=
@Mathlib.Tactic.Ring.cast_pos Real Real.instCommSemiring
  c15

noncomputable def p21336 :=
@Mathlib.Meta.NormNum.isNat_ofNat Real
  c5
  c15

noncomputable def p21337 :=
@p21334
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
      (Int.negOfNat 918231))
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@p21335 918231
    (@p21336 918231
      (@Eq.refl Real
        (@OfNat.ofNat Real 918231
          (@instOfNatAtLeastTwo Real 918231
            (@AddMonoidWithOne.toNatCast Real
              c5)
            (Mathlib.Meta.NormNum.instAtLeastTwo 918229))))))

noncomputable def p21338 :=
@Mathlib.Tactic.Ring.Common.add_mul Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    918231)
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
      (Int.negOfNat 918231))
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))

noncomputable def p21339 :=
@Mathlib.Tactic.Ring.Common.mul_add Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    918231)
  (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (Int.negOfNat 1))
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (Int.negOfNat 918231))

noncomputable def p21340 :=
@Mathlib.Meta.NormNum.IsInt.to_raw_eq Real
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      918231)
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 1)))
  (Int.negOfNat 918231)

noncomputable def p21341 :=
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
    918231)
  (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (Int.negOfNat 1))

noncomputable def p21342 :=
@p21341 (Int.ofNat 918231) (Int.negOfNat 1) (Int.negOfNat 918231)
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
      918231)
    918231
    (@Mathlib.Meta.NormNum.IsNat.of_raw Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      918231))

noncomputable def p21343 :=
@p21339
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 918231))
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@p21340 (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (p21342
      (@Mathlib.Meta.NormNum.IsInt.of_raw Real
        (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing)) (Int.negOfNat 1))
      (@Eq.refl Int (Int.negOfNat 918231))))
  (@Mathlib.Tactic.Ring.Common.mul_zero Real Real.instCommSemiring
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      918231))

noncomputable def p21344 :=
@p21338
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 918231))
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (p21343
    (@Mathlib.Tactic.Ring.Common.add_pf_add_zero Real Real.instCommSemiring
      (@HAdd.hAdd Real Real Real
        (@instHAdd Real
          (@Distrib.toAdd Real
            (@instDistribOfSemiring Real c0)))
        (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
          (Int.negOfNat 918231))
        (@OfNat.ofNat Real 0
          (@Zero.toOfNat0 Real
            (@MulZeroClass.toZero Real
              (@instMulZeroClassOfSemiring Real c0)))))))

noncomputable def p21345 :=
p21344
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
        (Int.negOfNat 918231))
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))))

noncomputable def p21346 :=
p21332
  (p21337
    (p3726 p3727
      (p3728
        (@Mathlib.Meta.NormNum.IsInt.to_raw_eq Real p3729 (Int.negOfNat 1)
          (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
          (p3733 (@Eq.refl Int (Int.negOfNat 1))))
        c65))
    p21345)

noncomputable def p21347 :=
@Mathlib.Tactic.Ring.Common.sub_congr Real Real.commRing p21325
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      1019031)
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

noncomputable def p21348 :=
@p3744 p21310
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      1019031)
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
      1019031)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))

noncomputable def p21349 :=
p21348
  (p3746
    (p3747
      (@Nat.cast_one Real
        c5)))
  (@Mathlib.Tactic.Ring.cast_pos Real Real.instCommSemiring p21310 1019031
    (@Mathlib.Meta.NormNum.isNat_ofNat Real
      c5
      p21310 1019031
      (@Eq.refl Real
        (@OfNat.ofNat Real 1019031
          (@instOfNatAtLeastTwo Real 1019031
            (@AddMonoidWithOne.toNatCast Real
              c5)
            (Mathlib.Meta.NormNum.instAtLeastTwo 1019029))))))

noncomputable def p21350 :=
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
      1019031)
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
      1019031)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))

noncomputable def p21351 :=
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
    1019031)
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1019031)

noncomputable def p21352 :=
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
      1019031))
  1019031

noncomputable def p21353 :=
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
    1019031)
  1 1019031

noncomputable def p21354 :=
@p21353 1019031
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
    1019031)
  (@Eq.refl Nat 1019031)

noncomputable def p21355 :=
@p21351
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
      1019031)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@p21352
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    p21354)

noncomputable def p21356 :=
p21355
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
        1019031)
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))))

noncomputable def p21357 :=
@p21350
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
      1019031)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  p21356

noncomputable def p21358 :=
p21357
  (@Mathlib.Tactic.Ring.Common.zero_mul Real Real.instCommSemiring
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))
      (@Nat.rawCast Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne Real
          (@NonAssocSemiring.toAddCommMonoidWithOne Real
            (@Semiring.toNonAssocSemiring Real c0)))
        1019031)
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))))

noncomputable def p21359 :=
p21358
  (@Mathlib.Tactic.Ring.Common.add_pf_add_zero Real Real.instCommSemiring
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))
      (@Nat.rawCast Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne Real
          (@NonAssocSemiring.toAddCommMonoidWithOne Real
            (@Semiring.toNonAssocSemiring Real c0)))
        1019031)
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))))

noncomputable def p21360 :=
@p21347
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
      1019031)
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))
      p6055
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))))
  (p21349 p21359)

noncomputable def p21361 :=
@Mathlib.Tactic.Ring.Common.sub_pf Real Real.commRing
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      1019031)
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

noncomputable def p21362 :=
@p21361
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
      1019031)
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

noncomputable def p21363 :=
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
    1019031)

noncomputable def p21364 :=
p21362
  (p21363
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

noncomputable def p21365 :=
@Mathlib.Tactic.Ring.Common.add_pf_add_overlap Real Real.instCommSemiring
  (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (Int.negOfNat 918231))
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1019031)
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

noncomputable def p21366 :=
@Mathlib.Meta.NormNum.IsNat.to_raw_eq Real
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 918231))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      1019031))
  100800
  (@Mathlib.Meta.NormNum.instAddMonoidWithOne Real
    (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing)))

noncomputable def p21367 :=
@Mathlib.Meta.NormNum.isInt_add Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0))))
  (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (Int.negOfNat 918231))
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1019031)
  (Int.negOfNat 918231) (Int.ofNat 1019031)

noncomputable def p21368 :=
@p21367 (Int.ofNat 100800)
  (@Eq.refl (Real → Real → Real)
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))))
  (@Mathlib.Meta.NormNum.IsInt.of_raw Real
    (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing)) (Int.negOfNat 918231))
  (@Mathlib.Meta.NormNum.IsNat.to_isInt Real
    (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      1019031)
    1019031
    (@Mathlib.Meta.NormNum.IsNat.of_raw Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      1019031))

noncomputable def p21369 :=
@Mathlib.Meta.NormNum.IsInt.to_isNat Real
  (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 918231))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      1019031))
  100800 (p21368 (@Eq.refl Int (Int.ofNat 100800)))

noncomputable def p21370 :=
p21346
  (p21360
    (p6091 (p6097 p6106) p6115)
    p21364)
  (p21365 (p21366 p21369)
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

noncomputable def p21371 :=
@Mathlib.Tactic.Ring.of_eq Real
  (@HAdd.hAdd Real Real Real
    c35
    p21327 (p6053 p3713))
  c25
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (p21330 p21370
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

noncomputable def p21372 :=
@congrArg Real Prop
  (@HAdd.hAdd Real Real Real
    c35
    p21327 (p6053 p3713))
  c25
  (fun (_a : Real) =>
    @LT.lt Real c29 _a
      (@OfNat.ofNat Real 0
        c49))
  (p21371
    (@Mathlib.Tactic.Ring.cast_zero Real Real.instCommSemiring
      c25
      (@Mathlib.Meta.NormNum.isNat_ofNat Real
        c5
        c25 0
        (@Nat.cast_zero Real
          c5))))

noncomputable def p21373 :=
@HAdd.hAdd Real Real Real
  (@instHAdd Real (@Distrib.toAdd Real (@instDistribOfSemiring Real Real.semiring)))
  (@HMul.hMul Real Real Real
    (@instHMul Real
      c51)
    c30
    c14)
  p21326

noncomputable def p21374 :=
@Mathlib.Tactic.Linarith.add_neg Real Real.semiring Real.partialOrder Real.instIsStrictOrderedRing
  (@HMul.hMul Real Real Real
    (@instHMul Real
      c51)
    c30
    c14)
  p21326

noncomputable def p21375 :=
@Mathlib.Tactic.Linarith.mul_neg Real Real.instRing Real.partialOrder Real.instIsStrictOrderedRing
  (@Neg.neg Real
    c36
    c23)
  c40
  (@neg_neg_of_pos Real Real.instAddCommGroup Real.partialOrder Real.instIsOrderedAddMonoid
    c23
    (@Mathlib.Tactic.Linarith.zero_lt_one Real Real.semiring Real.partialOrder Real.instIsStrictOrderedRing))

noncomputable def p21376 :=
@Mathlib.Meta.NormNum.isNat_lt_true Real Real.semiring Real.partialOrder Real.instIsOrderedRing
  (@FloorSemiring.instCharZero Real (@Ring.toSemiring Real Real.instRing) Real.partialOrder
    c26)
  c25
  c40
  0 918231
  (@Mathlib.Meta.NormNum.isNat_ofNat Real
    c5
    c25 0
    (@Nat.cast_zero Real
      c5))

noncomputable def p21377 :=
p21376
  (@Mathlib.Meta.NormNum.isNat_ofNat Real
    c5
    c30
    918231
    (@Eq.refl Real
      (@OfNat.ofNat Real 918231
        (@instOfNatAtLeastTwo Real 918231
          (@AddMonoidWithOne.toNatCast Real
            c5)
          (Mathlib.Meta.NormNum.instAtLeastTwo 918229)))))

noncomputable def p21378 :=
@HSub.hSub Real Real Real
  c52
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            c3))))
    p21310 p6033)

noncomputable def p21379 :=
p6171
  (p21378
    c17)

noncomputable def p21380 :=
@Mathlib.Tactic.CancelDenoms.derive_trans Real Real.instMul
  (p21378
    c17)

noncomputable def p21381 :=
@p21380
  (p21378
    c17)

noncomputable def p21382 :=
@p21381
  (@OfNat.ofNat Real 1000
    (@instOfNatAtLeastTwo Real 1000
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 998)))

noncomputable def p21383 :=
@congrArg Real (Real → Real)
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            c3))))
    p21310 p6033)

noncomputable def p21384 :=
@p21383
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            c3))))
    p21310 p6033)

noncomputable def p21385 :=
@congrFun' Real Real p21378 p21378
  (p21384
    (@HSub.hSub Real Real Real
      c24)
    (p21321 (@Eq.refl Real p6033)))
  c18

noncomputable def p21386 :=
@p6180
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            c3))))
    p21310 p6033)

noncomputable def p21387 :=
@p21386
  c18
  p21325

noncomputable def p21388 :=
@p21387
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real
          (@DivisionSemiring.toSemiring Real
            c3))))
    p3705 (p6050 Real.pi))

noncomputable def p21389 :=
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
  p21310

noncomputable def p21390 :=
@p6185 p21310 p6033 p21325
  (@rfl Real p21389)
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

noncomputable def p21391 :=
@Eq.mp
  (@LT.lt Real c29
    p21379
    c31)
  (@LT.lt Real c29
    p21326
    c31)
  (@congrArg Real Prop p21379 p21326
    (fun (_a : Real) =>
      @LT.lt Real c29 _a
        c50)
    (@p21382 p21326 p21385
      (p21388 p21390 p6207)))

noncomputable def p21392 :=
@Mathlib.Tactic.Linarith.mul_neg Real Real.instRing Real.partialOrder Real.instIsStrictOrderedRing
  (p21378
    c17)

noncomputable def p21393 :=
@Mathlib.Tactic.Linarith.sub_neg_of_lt Real Real.instRing Real.partialOrder Real.instIsOrderedRing
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            c3))))
    p21310 p6033)

noncomputable def p21394 :=
fun
    (a :
      p21323
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (@OfNat.ofNat Real 32
            (@instOfNatAtLeastTwo Real 32 Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 31 (instOfNatNat 31))
                c64)))
          Real.pi)) =>
  @Mathlib.Tactic.Linarith.lt_irrefl Real Real.instPreorder
    c25
    (p21328 p21372
      (@Mathlib.Tactic.Linarith.add_neg Real Real.semiring Real.partialOrder Real.instIsStrictOrderedRing
        p21373
        (@HMul.hMul Real Real Real
          (@instHMul Real
            c51)
          c38
          p3713)
        (p21374 (p21375 (p21377 (@Eq.refl Bool false)))
          (p21391
            (@p21392
              (@OfNat.ofNat Real 1000
                (@instOfNatAtLeastTwo Real 1000 Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 999 (instOfNatNat 999))
                    c63)))
              (@p21393
                (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                  (@OfNat.ofNat Real 32
                    (@instOfNatAtLeastTwo Real 32 Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 31 (instOfNatNat 31))
                        c64)))
                  Real.pi)
                a)
              (p6212 (@Eq.refl Bool false)))))
        (@Mathlib.Tactic.Linarith.mul_neg Real Real.instRing Real.partialOrder Real.instIsStrictOrderedRing
          p3713
          c38
          p3995 (p6214 (@Eq.refl Bool false)))))

noncomputable def p21395 :=
@Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal d57)
  (hardyZApproximantRS
    (@OfScientific.ofScientific Real c2 101903100
      true 5))
  true p19930 p19931

noncomputable def p21396 :=
@Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.fstVal d57) p19930
  p19931 p19933 p19934
  (@p21395 p19933 p19934
    (@Eq.refl Real
      (hardyZApproximantRS
        (@OfScientific.ofScientific Real c2 101903100
          true 5)))
    d257)

noncomputable def p21397 :=
@Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal d57)
  (hardyZApproximantRS
    (@OfScientific.ofScientific Real c2 102026300
      true 5))
  false p20574 p20575

noncomputable def p21398 :=
@Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.sndVal d57) p20574
  p20575 p20577 p20578
  (@p21397 p20577 p20578
    (@Eq.refl Real
      (hardyZApproximantRS
        (@OfScientific.ofScientific Real c2 102026300
          true 5)))
    d270)

noncomputable def p21399 :=
@Zeta.Certificates.ZIntervalRS.Certificate.mk d57
  (@Eq.mpr p21309 p21311
    (@id (@Eq Prop p21309 p21311)
      (@Eq.trans Prop p21309 p21311 p21311
        (p21313 (p21314 (@Eq.refl Real p6033)))
        (p21317 (p21321 (@Eq.refl Real p6033)))))
    (p21322 p21394))
  (BSN.mul_neg_of_neg_pos_r (Zeta.Certificates.ZIntervalRS.fstVal d57)
    (Zeta.Certificates.ZIntervalRS.sndVal d57)
    (p21396 (Eq.refl true) (Eq.refl true) (Eq.refl true))
    (p21398 (Eq.refl true) (Eq.refl true)
      (Eq.refl true)))

noncomputable def p21400 :=
@Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal d57)
  (hardyZErrorBoundRS (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE d57)))
  true false p19930 p19931 p19933

noncomputable def p21401 :=
@p21400 p19934 5936636289 549755813888 201
  549755813888
  (@p21395 p19933 p19934
    (@Eq.refl Real
      (hardyZApproximantRS
        (@OfScientific.ofScientific Real c2 101903100
          true 5)))
    d257)

noncomputable def p21402 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZErrorBoundRS (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE d57)))
  (hardyZErrorBoundRS
    (@OfScientific.ofScientific Real c2 101903100
      true 5))
  false 5936636289 549755813888

noncomputable def p21403 :=
p21401
  (@p21402 201 549755813888
    (@Eq.refl Real
      (hardyZErrorBoundRS
        (@OfScientific.ofScientific Real c2 101903100
          true 5)))
    d271)

noncomputable def p21404 :=
@Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal d57)
  (hardyZErrorBoundRS (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE d57)))
  false false p20574 p20575 p20577

noncomputable def p21405 :=
@p21404 p20578 5927676689 549755813888 201
  549755813888
  (@p21397 p20577 p20578
    (@Eq.refl Real
      (hardyZApproximantRS
        (@OfScientific.ofScientific Real c2 102026300
          true 5)))
    d270)

noncomputable def p21406 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZErrorBoundRS (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE d57)))
  (hardyZErrorBoundRS
    (@OfScientific.ofScientific Real c2 102026300
      true 5))
  false 5927676689 549755813888

noncomputable def p21407 :=
p21405
  (@p21406 201 549755813888
    (@Eq.refl Real
      (hardyZErrorBoundRS
        (@OfScientific.ofScientific Real c2 102026300
          true 5)))
    d272)

theorem d273 : Zeta.Certificates.ZIntervalRS.Certificate d57 :=
p21399
  (p21403 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (p21407 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
end RHHeight1000.GramZero663

theorem solution : ∃ t ∈ Set.Ioo (1019.03100 : ℝ) (1020.26300 : ℝ), riemannZeta (1 / 2 + Complex.I * t) = 0 := by
  exact riemannZeta.exists_zero_of_zIntervalRS_certificate _ RHHeight1000.GramZero663.d273

#print axioms solution
