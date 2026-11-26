-- Prove2me | solution 1 for RHHeight1000.gram_zero664_exists
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-19T16:29:06.56117+00:00
-- url     : https://prove2.me/submissions/e4bd7804-4369-42ca-8ef4-234437700607

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

namespace RHHeight1000.GramZero664
noncomputable def p3 :=
@Mathlib.Meta.NormNum.isNat_pow Nat Nat.instSemiring
  (@HPow.hPow Nat Nat Nat
    (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))))
  (@OfNat.ofNat Nat 10 (instOfNatNat 10)) 5 10 5 100000

noncomputable def p4 :=
p3
  (@Eq.refl (Nat → Nat → Nat)
    (@HPow.hPow Nat Nat Nat
      (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))))
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
@Mathlib.Meta.NormNum.isNNRat_inv_pos NNRat (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield)
  NNRat.instCharZero
  (@Nat.cast NNRat
    (@AddMonoidWithOne.toNatCast NNRat
      (@AddCommMonoidWithOne.toAddMonoidWithOne NNRat
        (@NonAssocSemiring.toAddCommMonoidWithOne NNRat
          (@Semiring.toNonAssocSemiring NNRat
            (@DivisionSemiring.toSemiring NNRat (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield))))))
    100000)
  99999

noncomputable def p10 :=
@Mathlib.Meta.NormNum.IsNat.to_isNNRat NNRat
  (@DivisionSemiring.toSemiring NNRat (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield))
  (@Nat.cast NNRat
    (@AddMonoidWithOne.toNatCast NNRat
      (@AddCommMonoidWithOne.toAddMonoidWithOne NNRat
        (@NonAssocSemiring.toAddCommMonoidWithOne NNRat
          (@Semiring.toNonAssocSemiring NNRat
            (@DivisionSemiring.toSemiring NNRat (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield))))))
    100000)
  100000

noncomputable def p11 :=
p10
  (@Mathlib.Meta.NormNum.isNat_natCast NNRat
    (@AddCommMonoidWithOne.toAddMonoidWithOne NNRat
      (@NonAssocSemiring.toAddCommMonoidWithOne NNRat
        (@Semiring.toNonAssocSemiring NNRat
          (@DivisionSemiring.toSemiring NNRat (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield)))))
    100000 100000 (Mathlib.Meta.NormNum.IsNat.raw_refl 100000))

noncomputable def p382 :=
@Mathlib.Meta.NormNum.isRat_le_true Real
  (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField)) Real.linearOrder
  Real.instIsStrictOrderedRing
  (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
    true 5)
  (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
    true 5)
  (Int.ofNat 510133) (Int.ofNat 1021497) 500

noncomputable def p383 :=
@Mathlib.Meta.NormNum.isNNRat_nnratCast Real
  (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField))
  (@FloorSemiring.instCharZero Real Real.semiring Real.partialOrder
    (@FloorRing.toFloorSemiring Real Real.instRing Real.linearOrder Real.instFloorRing))
  (NNRat.divNat 102026600
    (@HPow.hPow Nat Nat Nat
      (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
      (@OfNat.ofNat Nat 10 (instOfNatNat 10)) 5))
  510133 500

noncomputable def p384 :=
@Mathlib.Meta.NormNum.isNNRat_divNat 102026600 102026600 510133
  (@HPow.hPow Nat Nat Nat
    (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
    (@OfNat.ofNat Nat 10 (instOfNatNat 10)) 5)
  100000 500 (Mathlib.Meta.NormNum.IsNat.raw_refl 102026600)

noncomputable def p385 :=
@Mathlib.Meta.NormNum.isNNRat_div NNRat (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield)
  (@Nat.cast NNRat
    (@AddMonoidWithOne.toNatCast NNRat
      (@AddCommMonoidWithOne.toAddMonoidWithOne NNRat
        (@NonAssocSemiring.toAddCommMonoidWithOne NNRat
          (@Semiring.toNonAssocSemiring NNRat
            (@DivisionSemiring.toSemiring NNRat (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield))))))
    102026600)
  (@Nat.cast NNRat
    (@AddMonoidWithOne.toNatCast NNRat
      (@AddCommMonoidWithOne.toAddMonoidWithOne NNRat
        (@NonAssocSemiring.toAddCommMonoidWithOne NNRat
          (@Semiring.toNonAssocSemiring NNRat
            (@DivisionSemiring.toSemiring NNRat (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield))))))
    100000)

noncomputable def p386 :=
@Mathlib.Meta.NormNum.isNNRat_mul NNRat
  (@DivisionSemiring.toSemiring NNRat (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield))
  (@HMul.hMul NNRat NNRat NNRat
    (@instHMul NNRat
      (@Distrib.toMul NNRat
        (@instDistribOfSemiring NNRat
          (@DivisionSemiring.toSemiring NNRat (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield))))))
  (@Nat.cast NNRat
    (@AddMonoidWithOne.toNatCast NNRat
      (@AddCommMonoidWithOne.toAddMonoidWithOne NNRat
        (@NonAssocSemiring.toAddCommMonoidWithOne NNRat
          (@Semiring.toNonAssocSemiring NNRat
            (@DivisionSemiring.toSemiring NNRat (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield))))))
    102026600)
  (@Inv.inv NNRat
    (@InvOneClass.toInv NNRat
      (@DivInvOneMonoid.toInvOneClass NNRat
        (@DivisionMonoid.toDivInvOneMonoid NNRat
          (@GroupWithZero.toDivisionMonoid NNRat
            (@DivisionSemiring.toGroupWithZero NNRat
              (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield))))))
    (@Nat.cast NNRat
      (@AddMonoidWithOne.toNatCast NNRat
        (@AddCommMonoidWithOne.toAddMonoidWithOne NNRat
          (@NonAssocSemiring.toAddCommMonoidWithOne NNRat
            (@Semiring.toNonAssocSemiring NNRat
              (@DivisionSemiring.toSemiring NNRat (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield))))))
      100000))

noncomputable def p387 :=
@Mathlib.Meta.NormNum.IsNat.to_isNNRat NNRat
  (@DivisionSemiring.toSemiring NNRat (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield))
  (@Nat.cast NNRat
    (@AddMonoidWithOne.toNatCast NNRat
      (@AddCommMonoidWithOne.toAddMonoidWithOne NNRat
        (@NonAssocSemiring.toAddCommMonoidWithOne NNRat
          (@Semiring.toNonAssocSemiring NNRat
            (@DivisionSemiring.toSemiring NNRat (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield))))))
    102026600)
  102026600

noncomputable def p388 :=
p387
  (@Mathlib.Meta.NormNum.isNat_natCast NNRat
    (@AddCommMonoidWithOne.toAddMonoidWithOne NNRat
      (@NonAssocSemiring.toAddCommMonoidWithOne NNRat
        (@Semiring.toNonAssocSemiring NNRat
          (@DivisionSemiring.toSemiring NNRat (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield)))))
    102026600 102026600 (Mathlib.Meta.NormNum.IsNat.raw_refl 102026600))

noncomputable def p389 :=
@p386 102026600 1 510133 1 100000 500
  200
  (@Eq.refl (NNRat → NNRat → NNRat)
    (@HMul.hMul NNRat NNRat NNRat
      (@instHMul NNRat
        (@Distrib.toMul NNRat
          (@instDistribOfSemiring NNRat
            (@DivisionSemiring.toSemiring NNRat (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield)))))))
  p388 (@p9 1 p11)

noncomputable def p390 :=
@p382 1000
  (@Mathlib.Meta.NormNum.IsNNRat.to_isRat Real
    (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
      true 5)
    510133 500
    (@Mathlib.Meta.NormNum.isNNRat_ofScientific_of_true Real
      (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField)) 102026600
      5 510133 500
      (p383
        (p384 p4
          (@p385 510133 500
            (p389 (@Eq.refl Nat (Nat.mul 102026600 1))
              (@Eq.refl Nat 100000)))))))

noncomputable def p391 :=
@Mathlib.Meta.NormNum.isNNRat_nnratCast Real
  (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField))
  (@FloorSemiring.instCharZero Real Real.semiring Real.partialOrder
    (@FloorRing.toFloorSemiring Real Real.instRing Real.linearOrder Real.instFloorRing))
  (NNRat.divNat 102149700
    (@HPow.hPow Nat Nat Nat
      (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
      (@OfNat.ofNat Nat 10 (instOfNatNat 10)) 5))
  1021497 1000

noncomputable def p392 :=
@Mathlib.Meta.NormNum.isNNRat_divNat 102149700 102149700 1021497
  (@HPow.hPow Nat Nat Nat
    (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
    (@OfNat.ofNat Nat 10 (instOfNatNat 10)) 5)
  100000 1000 (Mathlib.Meta.NormNum.IsNat.raw_refl 102149700)

noncomputable def p393 :=
@Mathlib.Meta.NormNum.isNNRat_div NNRat (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield)
  (@Nat.cast NNRat
    (@AddMonoidWithOne.toNatCast NNRat
      (@AddCommMonoidWithOne.toAddMonoidWithOne NNRat
        (@NonAssocSemiring.toAddCommMonoidWithOne NNRat
          (@Semiring.toNonAssocSemiring NNRat
            (@DivisionSemiring.toSemiring NNRat (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield))))))
    102149700)
  (@Nat.cast NNRat
    (@AddMonoidWithOne.toNatCast NNRat
      (@AddCommMonoidWithOne.toAddMonoidWithOne NNRat
        (@NonAssocSemiring.toAddCommMonoidWithOne NNRat
          (@Semiring.toNonAssocSemiring NNRat
            (@DivisionSemiring.toSemiring NNRat (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield))))))
    100000)

noncomputable def p394 :=
@Mathlib.Meta.NormNum.isNNRat_mul NNRat
  (@DivisionSemiring.toSemiring NNRat (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield))
  (@HMul.hMul NNRat NNRat NNRat
    (@instHMul NNRat
      (@Distrib.toMul NNRat
        (@instDistribOfSemiring NNRat
          (@DivisionSemiring.toSemiring NNRat (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield))))))
  (@Nat.cast NNRat
    (@AddMonoidWithOne.toNatCast NNRat
      (@AddCommMonoidWithOne.toAddMonoidWithOne NNRat
        (@NonAssocSemiring.toAddCommMonoidWithOne NNRat
          (@Semiring.toNonAssocSemiring NNRat
            (@DivisionSemiring.toSemiring NNRat (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield))))))
    102149700)
  (@Inv.inv NNRat
    (@InvOneClass.toInv NNRat
      (@DivInvOneMonoid.toInvOneClass NNRat
        (@DivisionMonoid.toDivInvOneMonoid NNRat
          (@GroupWithZero.toDivisionMonoid NNRat
            (@DivisionSemiring.toGroupWithZero NNRat
              (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield))))))
    (@Nat.cast NNRat
      (@AddMonoidWithOne.toNatCast NNRat
        (@AddCommMonoidWithOne.toAddMonoidWithOne NNRat
          (@NonAssocSemiring.toAddCommMonoidWithOne NNRat
            (@Semiring.toNonAssocSemiring NNRat
              (@DivisionSemiring.toSemiring NNRat (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield))))))
      100000))

noncomputable def p395 :=
@Mathlib.Meta.NormNum.IsNat.to_isNNRat NNRat
  (@DivisionSemiring.toSemiring NNRat (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield))
  (@Nat.cast NNRat
    (@AddMonoidWithOne.toNatCast NNRat
      (@AddCommMonoidWithOne.toAddMonoidWithOne NNRat
        (@NonAssocSemiring.toAddCommMonoidWithOne NNRat
          (@Semiring.toNonAssocSemiring NNRat
            (@DivisionSemiring.toSemiring NNRat (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield))))))
    102149700)
  102149700

noncomputable def p396 :=
p395
  (@Mathlib.Meta.NormNum.isNat_natCast NNRat
    (@AddCommMonoidWithOne.toAddMonoidWithOne NNRat
      (@NonAssocSemiring.toAddCommMonoidWithOne NNRat
        (@Semiring.toNonAssocSemiring NNRat
          (@DivisionSemiring.toSemiring NNRat (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield)))))
    102149700 102149700 (Mathlib.Meta.NormNum.IsNat.raw_refl 102149700))

noncomputable def p397 :=
@p394 102149700 1 1021497 1 100000 1000
  100
  (@Eq.refl (NNRat → NNRat → NNRat)
    (@HMul.hMul NNRat NNRat NNRat
      (@instHMul NNRat
        (@Distrib.toMul NNRat
          (@instDistribOfSemiring NNRat
            (@DivisionSemiring.toSemiring NNRat (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield)))))))
  p396 (@p9 1 p11)

noncomputable def p398 :=
p390
  (@Mathlib.Meta.NormNum.IsNNRat.to_isRat Real
    (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
      true 5)
    1021497 1000
    (@Mathlib.Meta.NormNum.isNNRat_ofScientific_of_true Real
      (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField)) 102149700
      5 1021497 1000
      (p391
        (p392 p4
          (@p393 1021497 1000
            (p397 (@Eq.refl Nat (Nat.mul 102149700 1))
              (@Eq.refl Nat 100000)))))))

theorem d63 : @LE.le Real
  (@Preorder.toLE Real
    (@PartialOrder.toPreorder Real
      (@SemilatticeInf.toPartialOrder Real
        (@Lattice.toSemilatticeInf Real
          (@DistribLattice.toLattice Real (@instDistribLatticeOfLinearOrder Real Real.linearOrder))))))
  (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
    true 5)
  (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
    true 5) :=
p398 (Eq.refl true)

noncomputable def d64 :=
@NonemptyInterval.mk Real Real.instLE
  (@Prod.mk Real Real
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
      true 5)
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
      true 5))
  d63

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

noncomputable def p2042 :=
@Enclosure.Real.IsNear.recentre' (Real.log Real.pi) false 78665238759 68719476736 2
  68719476736 78665238759 68719476736 1 34359738368

noncomputable def p2043 :=
@BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1
  1000000000000000 p497 p593 p499 p593
  157330477519 137438953472

noncomputable def p2046 :=
nat_lit
  28112249726568391589047516573961016100230695266595138796645898844068455765826150661746425623361233424082198271039924780088271379132689863069221204238560183629201607644021685675098964741933636681146646085450281554642234567670273398510595608388401361582887942310446147737587363843978980100496524524149645324535726971841246491625617094543039703127568346472270082785977497346976624911418331836820278316086423086221698714772627386990029610668989360984838503376478261856551986321583831120245376241683570873990542024084976461912564043669928266913234808138444564697009788556422071443556665104485951316241205417724454884855648838586880998728494388445042826471386528295148565814403457608975325084421742121394650813826944853845535730717079638892361862488354697476516361002681016858732631075345788689669322864575479543781416716836529222919811305834432880382494042916396369004063385142542944123203596085267144355012182693848192467538993321594614691095850768794488026694041566360767047538370072844536145465625

noncomputable def p2047 :=
nat_lit
  3004852088952768845920618744553278527204692828375153584392003179441110915259710236217584603096118328104680832169483210561589325374912009409850222660711266215775790384571551429890480172556385640686680474032161112410464266713994866393778433661006945913182018947418487320399615641795552072647902100183574245260251043675061202707045470229404510257054669582810821424393350840091252955407241565764109916492793914631945586814885644558726210255466565212322672666804789077217737419201108469876131774340314495933866107672625386841546065679278379967588836860231971112056212051701786409418893940900332221197280978896706663592437230896317804020812894593837818667147274729545133224953997584838639067106369936658157631771313490070272044892491227518160759585764692109951245393652651596149425400941367486350589239615552351659509511773702708987671624772355194695219991156759969388230106513516518404759588330543927959707500174897764780405058368784771513978993918218553854643944162112070721962901566067768789252375

noncomputable def p2048 :=
nat_lit
  9407440773224172681608700800935793010623091823451060729311335758097884212674519651449525711559811298259706715802174741819386929788979265886490710442570602643258333481940675986925031166385219002468759325425871585023540930321333085653246210767457816937546151967387697762867366118158349272438706119700156825534863826747864802135549084951496534996548721807020772886548043755609972182010967717941572151546388230735108166873457723560431535436103604158287676565659967228712317028040615680390038739538457534455011980724218179173567216927517217433242876173265519116175068208539039413233240521992767665208397431498233209472829716964273590741575120542767682365189084066271996528146206849186493650578605643960924800580523089630169611245121301536400385494384892405066700887668265289347023652942104761440574085006181174048868346007483392864104239217621438509276641851575397778814711237716004915415172882101120782235589971491833178320649134371141612801731087615746635195857438501796739603490909375

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

noncomputable def p2059 :=
nat_lit
  28112249726568907460877008869448272292468917300661539822477485878707621656431906701706028048427306405265710875708483116966759122895385544819830156795244674632541754443830707273941294995089033428356490509282885064723300802697449921482133275722309366483149434048383907108566415254354824568783131399250272268358636149329667001700939403651929971686504139771582648399892312746886479683987028568936035758161816431633261845913657154371769303950313408559248382929642419083165632911770392995359037468429404240879124068294464716235537436856506956042298285974223689290858683659401065292151897123451222064736785585235431221018049649439372563886315701595281098304271750270872968926297946531264926919670251846171449719442723791463222179752851839175213475316233298067645959528625158496875321419100946334304561169749638234378999637386874925356928373561848382418558332943231405031307075642747796504407594783753774170078472723429650004559240716727362113831551503740797630206625579385418783397570072844536145465625

noncomputable def p2060 :=
nat_lit
  3004852088952827258288190099535631124168114566284207337970056940674351348135361224185106093952970606535695727260345158671755721791400581520330370588532138341756984687453720988491484964511734575418260368734151156841153407162414876752839676953376108288208692242085462695739689384148522826788437087822586887497413203836902051755317535914550644620893279412055445950685345590921102798162921389184656775637861449676147100406454604972151425938388347444151335265623299723631195888111839512355504135172676829460307444689905847047303792776880640602849950094546379376735308619361158700081330061247667415156371627619475851554930068955581234134465848503479162906009209317293239008407944225919387784154374053414813625507104264554954609847197828864338540915550432814784915042683957287234778459934928332697833954180309734050028617392891921873102879555622224078778988254742261073027159089045085149064194991842552848313525138533726320734385011066819633493617444930793199670070398927329942668181566067768789252375

noncomputable def p2061 :=
nat_lit
  9407440773224506529176568857500651144538144565583026311565562241310742360945416609514739181585737663471595495472140923899131384509152239269388817553807034752862166542219692542995804337854598506316907415511184151817482264628622313716122996615543595005129428372116317285987632920507038000124579601150058617461875221973393380924109746168913932623510245472899670149930298259253405611312385676949967940212803800193139782709063837214988572438699173613449788059279786984431338912400273520515747622264511830981712117559767214914416220668489073254135684909167805776893455817185649108869135643881492499080235371375755823857514528492866785157313469780272824393257511939999548644659051837740928586042457828897318497978608139105011180034468394090072098785278119541968136350138141050633792133675665148198849246063996402023436753126022992248443806354116118325467465605265682353640993215005430174748643823987912828900106265897437245293863251493678193606984591788436589065317713701796739603490909375

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
Enclosure.Real.IsNear (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))
  false 759250125 1073741824 1 8589934592

noncomputable def p2077 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2))) false
  12148002000 17179869184 2 17179869184

noncomputable def p2078 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 2)) 24296003999
  17179869184 1 17179869184 6074000999 6074001001

noncomputable def p2079 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 2))
  (Real.sqrt
    (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
      (@Nat.cast Real Real.instNatCast 2) (@Nat.cast Real Real.instNatCast 1)))
  false 24296003999 17179869184

noncomputable def p2080 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
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
Enclosure.Real.IsNear (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))
  false 97184016000 137438953472 16 137438953472

noncomputable def p2084 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2))) false
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
Enclosure.Real.IsNear (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))
  false 4959401049 8589934592 1 8589934592

noncomputable def p2093 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3))) false
  9918802098 17179869184 2 17179869184

noncomputable def p2094 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 3)) 29756406295
  17179869184 1 17179869184 4959401048 4959401050

noncomputable def p2095 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 3))
  (Real.sqrt
    (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
      (@Nat.cast Real Real.instNatCast 3) (@Nat.cast Real Real.instNatCast 1)))
  false 29756406295 17179869184

noncomputable def p2096 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
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
Enclosure.Real.IsNear (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))
  false 79350416784 137438953472 16 137438953472

noncomputable def p2100 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3))) false
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
    (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
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
    (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
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
Enclosure.Real.IsNear (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))
  false 8589934591 17179869184 1 17179869184

noncomputable def p2159 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4))) false
  8589934591 17179869184 1 17179869184

noncomputable def p2160 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 4)) 34359738369
  17179869184 1 17179869184 4294967295 4294967296

noncomputable def p2161 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 4))
  (Real.sqrt
    (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
      (@Nat.cast Real Real.instNatCast 4) (@Nat.cast Real Real.instNatCast 1)))
  false 34359738369 17179869184

noncomputable def p2162 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
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
Enclosure.Real.IsNear (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))
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
Enclosure.Real.IsNear (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))
  false 1920767767 4294967296 1 8589934592

noncomputable def p2183 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5))) false
  7683071068 17179869184 2 17179869184

noncomputable def p2184 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 5)) 38415355339
  17179869184 1 17179869184 3841535533 3841535535

noncomputable def p2185 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 5))
  (Real.sqrt
    (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
      (@Nat.cast Real Real.instNatCast 5) (@Nat.cast Real Real.instNatCast 1)))
  false 38415355339 17179869184

noncomputable def p2186 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
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
Enclosure.Real.IsNear (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))
  false 61464568544 137438953472 16 137438953472

noncomputable def p2190 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5))) false
  1920767767 4294967296 1 8589934592

theorem d111 : p2189 :=
@p2190 61464568544 137438953472 16 137438953472
  d110 (Eq.refl true)

noncomputable def p2191 :=
nat_lit 554522696895959841336459264

noncomputable def p2192 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
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
Enclosure.Real.IsNear (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6)))
  false 7013652225 17179869184 1 17179869184

noncomputable def p2201 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6))) false
  7013652225 17179869184 1 17179869184

noncomputable def p2202 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 6)) 42081913349
  17179869184 1 17179869184 3506826112 3506826113

noncomputable def p2203 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 6))
  (Real.sqrt
    (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
      (@Nat.cast Real Real.instNatCast 6) (@Nat.cast Real Real.instNatCast 1)))
  false 42081913349 17179869184

noncomputable def p2204 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
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
Enclosure.Real.IsNear (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6)))
  false 56109217800 137438953472 8 137438953472

theorem d115 : p2207 :=
@p2201 56109217800 137438953472 8 137438953472
  d114 (Eq.refl true)

noncomputable def p2208 :=
nat_lit 602230021555239699653591040

noncomputable def p2209 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
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
Enclosure.Real.IsNear (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7)))
  false 6493380203 17179869184 1 17179869184

noncomputable def p2218 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7))) false
  6493380203 17179869184 1 17179869184

noncomputable def p2219 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 7)) 45453661417
  17179869184 1 17179869184 3246690101 3246690102

noncomputable def p2220 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 7))
  (Real.sqrt
    (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
      (@Nat.cast Real Real.instNatCast 7) (@Nat.cast Real Real.instNatCast 1)))
  false 45453661417 17179869184

noncomputable def p2221 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
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
Enclosure.Real.IsNear (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7)))
  false 51947041624 137438953472 8 137438953472

theorem d119 : p2224 :=
@p2218 51947041624 137438953472 8 137438953472
  d118 (Eq.refl true)

noncomputable def p2225 :=
nat_lit 643555985949696828723167232

noncomputable def p2226 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
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
Enclosure.Real.IsNear (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8)))
  false 759250125 2147483648 1 8589934592

noncomputable def p2234 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8))) false
  6074001000 17179869184 2 17179869184

noncomputable def p2235 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 8)) 48592007999
  17179869184 1 17179869184 3037000499 3037000501

noncomputable def p2236 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 8))
  (Real.sqrt
    (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
      (@Nat.cast Real Real.instNatCast 8) (@Nat.cast Real Real.instNatCast 1)))
  false 48592007999 17179869184

noncomputable def p2237 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
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
Enclosure.Real.IsNear (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8)))
  false 48592008000 137438953472 16 137438953472

noncomputable def p2241 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8))) false
  759250125 2147483648 1 8589934592

theorem d123 : p2240 :=
@p2241 48592008000 137438953472 16 137438953472
  d122 (Eq.refl true)

noncomputable def p2242 :=
nat_lit 680008069884511480266620928

noncomputable def p2243 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
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
Enclosure.Real.IsNear (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9)))
  false 5726623061 17179869184 1 17179869184

noncomputable def p2251 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9))) false
  5726623061 17179869184 1 17179869184

noncomputable def p2252 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 9)) 51539607553
  17179869184 1 17179869184 2863311530 2863311531

noncomputable def p2253 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 9))
  (Real.sqrt
    (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
      (@Nat.cast Real Real.instNatCast 9) (@Nat.cast Real Real.instNatCast 1)))
  false 51539607553 17179869184

noncomputable def p2254 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
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
Enclosure.Real.IsNear (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9)))
  false 45812984488 137438953472 8 137438953472

theorem d127 : p2257 :=
@p2251 45812984488 137438953472 8 137438953472
  d126 (Eq.refl true)

noncomputable def p2258 :=
nat_lit 712615570104769214689574912

noncomputable def p2259 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
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
Enclosure.Real.IsNear (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 10)))
  false 5432751653 17179869184 1 17179869184

noncomputable def p2267 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 10))) false
  5432751653 17179869184 1 17179869184

noncomputable def p2268 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 10)) 54327516525
  17179869184 1 17179869184 2716375826 2716375827

noncomputable def p2269 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 10))
  (Real.sqrt
    (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
      (@Nat.cast Real Real.instNatCast 10) (@Nat.cast Real Real.instNatCast 1)))
  false 54327516525 17179869184

noncomputable def p2270 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
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
Enclosure.Real.IsNear (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 10)))
  false 43462013224 137438953472 8 137438953472

theorem d131 : p2273 :=
@p2267 43462013224 137438953472 8 137438953472
  d130 (Eq.refl true)

noncomputable def p2274 :=
nat_lit 742112642020618540985352192

noncomputable def p2275 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
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
Enclosure.Real.IsNear (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 11)))
  false 5179925457 17179869184 1 17179869184

noncomputable def p2283 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 11))) false
  5179925457 17179869184 1 17179869184

noncomputable def p2284 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 11)) 56979180031
  17179869184 1 17179869184 2589962728 2589962729

noncomputable def p2285 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 11))
  (Real.sqrt
    (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
      (@Nat.cast Real Real.instNatCast 11) (@Nat.cast Real Real.instNatCast 1)))
  false 56979180031 17179869184

noncomputable def p2286 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
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
Enclosure.Real.IsNear (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 11)))
  false 41439403656 137438953472 8 137438953472

theorem d135 : p2289 :=
@p2283 41439403656 137438953472 8 137438953472
  d134 (Eq.refl true)

noncomputable def p2290 :=
nat_lit 769041358879192117577515008

noncomputable def p2291 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
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
Enclosure.Real.IsNear (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 12)))
  false 4959401049 17179869184 1 17179869184

noncomputable def p2299 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 12))) false
  4959401049 17179869184 1 17179869184

noncomputable def p2300 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 12)) 59512812589
  17179869184 1 17179869184 2479700524 2479700525

noncomputable def p2301 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 12))
  (Real.sqrt
    (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
      (@Nat.cast Real Real.instNatCast 12) (@Nat.cast Real Real.instNatCast 1)))
  false 59512812589 17179869184

noncomputable def p2302 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
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
Enclosure.Real.IsNear (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 12)))
  false 39675208392 137438953472 8 137438953472

theorem d139 : p2305 :=
@p2299 39675208392 137438953472 8 137438953472
  d138 (Eq.refl true)

noncomputable def p2306 :=
Enclosure.Real.IsNear
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  false 884279719003555 140737488355328 1

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

noncomputable def p2321 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 4 1)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) Real.pi Real.pi) 4 1
  0 1

noncomputable def p2323 :=
Enclosure.Real.IsNear
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 8 1)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) Real.pi Real.pi) Real.pi))
  false

noncomputable def p2324 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 8 1)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) Real.pi Real.pi) Real.pi)
  8 1

noncomputable def p2333 :=
nat_lit 2475880078570760549798248448

noncomputable def p2337 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 96 1)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) Real.pi Real.pi) 96 1
  0 1

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
  (@HPow.hPow Real Nat Real
    (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))
    (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)))
    12)
  (Enclosure.sfrac false 1 1) false 1

noncomputable def p2602 :=
nat_lit 2417851639229258349412352

noncomputable def p2630 :=
nat_lit 41538374868278621028243970633760768

noncomputable def p2632 :=
nat_lit 1267650600228229401496703205376000000000000000

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
          (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField))))))
  (@OfNat.ofNat Real 1
    (@One.toOfNat1 Real
      (@AddMonoidWithOne.toOne Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))))
  (@OfNat.ofNat Real 32
    (@instOfNatAtLeastTwo Real 32 Real.instNatCast
      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 31 (instOfNatNat 31))
        (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 30 (instOfNatNat 30))))))

noncomputable def p3710 :=
@HMul.hMul Real Real Real
  (@instHMul Real
    (@Distrib.toMul Real
      (@instDistribOfSemiring Real
        (@DivisionSemiring.toSemiring Real
          (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField))))))
  (@OfNat.ofNat Real 20
    (@instOfNatAtLeastTwo Real 20
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3711 :=
@OfNat.ofNat Real 63
  (@instOfNatAtLeastTwo Real 63
    (@AddMonoidWithOne.toNatCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real
            (@DivisionSemiring.toSemiring Real
              (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField)))))))
    (Mathlib.Meta.NormNum.instAtLeastTwo 61))

noncomputable def p3712 :=
@HMul.hMul Real Real Real
  (@instHMul Real
    (@Distrib.toMul Real
      (@instDistribOfSemiring Real
        (@DivisionSemiring.toSemiring Real
          (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField))))))
  (@OfNat.ofNat Real 1
    (@One.toOfNat1 Real
      (@AddMonoidWithOne.toOne Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))))
  p3711

noncomputable def p3713 :=
@HSub.hSub Real Real Real
  (@instHSub Real
    (@SubNegMonoid.toSub Real
      (@AddGroup.toSubNegMonoid Real
        (@AddGroupWithOne.toAddGroup Real
          (@Ring.toAddGroupWithOne Real
            (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField)))))))
  (p3710 Real.pi) p3712

noncomputable def p3726 :=
@Mathlib.Tactic.Ring.Common.neg_congr Real Real.commRing
  (@OfNat.ofNat Real 1
    (@One.toOfNat1 Real
      (@AddMonoidWithOne.toOne Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne Real
          (@NonAssocSemiring.toAddCommMonoidWithOne Real (@Semiring.toNonAssocSemiring Real Real.semiring))))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      1)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 1))
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))

noncomputable def p3727 :=
@Mathlib.Tactic.Ring.cast_pos Real Real.instCommSemiring
  (@OfNat.ofNat Real 1
    (@One.toOfNat1 Real
      (@AddMonoidWithOne.toOne Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne Real
          (@NonAssocSemiring.toAddCommMonoidWithOne Real (@Semiring.toNonAssocSemiring Real Real.semiring))))))
  1
  (@Mathlib.Meta.NormNum.isNat_ofNat Real
    (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing))
    (@OfNat.ofNat Real 1
      (@One.toOfNat1 Real
        (@AddMonoidWithOne.toOne Real
          (@AddCommMonoidWithOne.toAddMonoidWithOne Real
            (@NonAssocSemiring.toAddCommMonoidWithOne Real
              (@Semiring.toNonAssocSemiring Real Real.semiring))))))
    1
    (@Nat.cast_one Real
      (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing))))

noncomputable def p3728 :=
@Mathlib.Tactic.Ring.Common.neg_add Real Real.commRing
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    1)
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (Int.negOfNat 1))
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))

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
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
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
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    1)
  (Int.ofNat 1) (Int.negOfNat 1) p3731

noncomputable def p3733 :=
p3732
  (@Mathlib.Meta.NormNum.IsNat.to_isInt Real
    (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      1)
    1
    (@Mathlib.Meta.NormNum.IsNat.of_raw Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      1))

noncomputable def p3744 :=
@Mathlib.Tactic.Ring.Common.mul_congr Real Real.instCommSemiring
  (@OfNat.ofNat Real 1
    (@One.toOfNat1 Real
      (@AddMonoidWithOne.toOne Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      1)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))

noncomputable def p3746 :=
@Mathlib.Tactic.Ring.cast_pos Real Real.instCommSemiring
  (@OfNat.ofNat Real 1
    (@One.toOfNat1 Real
      (@AddMonoidWithOne.toOne Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))))
  1

noncomputable def p3747 :=
@Mathlib.Meta.NormNum.isNat_ofNat Real
  (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing))
  (@OfNat.ofNat Real 1
    (@One.toOfNat1 Real
      (@AddMonoidWithOne.toOne Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))))
  1

noncomputable def p3762 :=
@p3744
  (@OfNat.ofNat Real 32
    (@instOfNatAtLeastTwo Real 32 Real.instNatCast
      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 31 (instOfNatNat 31))
        (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 30 (instOfNatNat 30))))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      32)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      32)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))

noncomputable def p3763 :=
@Mathlib.Tactic.Ring.cast_pos Real Real.instCommSemiring
  (@OfNat.ofNat Real 32
    (@instOfNatAtLeastTwo Real 32 Real.instNatCast
      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 31 (instOfNatNat 31))
        (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 30 (instOfNatNat 30))))))
  32
  (@Mathlib.Meta.NormNum.isNat_ofNat Real
    (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing))
    (@OfNat.ofNat Real 32
      (@instOfNatAtLeastTwo Real 32 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 31 (instOfNatNat 31))
          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 30 (instOfNatNat 30))))))
    32
    (@Eq.refl Real
      (@OfNat.ofNat Real 32
        (@instOfNatAtLeastTwo Real 32
          (@AddMonoidWithOne.toNatCast Real
            (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing)))
          (Mathlib.Meta.NormNum.instAtLeastTwo 30)))))

noncomputable def p3764 :=
@Mathlib.Tactic.Ring.Common.add_mul Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    1)
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      32)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      32)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))

noncomputable def p3765 :=
@Mathlib.Tactic.Ring.Common.mul_add Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    1)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    32)
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    32)

noncomputable def p3766 :=
@Mathlib.Meta.NormNum.IsNat.to_raw_eq Real
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      1)
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      32))
  32

noncomputable def p3767 :=
@Mathlib.Meta.NormNum.isNat_mul Real (@CommSemiring.toSemiring Real Real.instCommSemiring)
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    1)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    32)
  1 32

noncomputable def p3768 :=
@p3767 32
  (@Eq.refl (Real → Real → Real)
    (@HMul.hMul Real Real Real
      (@instHMul Real
        (@Distrib.toMul Real
          (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (@Mathlib.Meta.NormNum.IsNat.of_raw Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    1)
  (@Mathlib.Meta.NormNum.IsNat.of_raw Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    32)
  (@Eq.refl Nat 32)

noncomputable def p3769 :=
@p3765
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      32)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (@p3766
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    p3768)

noncomputable def p3770 :=
p3769
  (@Mathlib.Tactic.Ring.Common.mul_zero Real Real.instCommSemiring
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      1))
  (@Mathlib.Tactic.Ring.Common.add_pf_add_zero Real Real.instCommSemiring
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      (@Nat.rawCast Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne Real
          (@NonAssocSemiring.toAddCommMonoidWithOne Real
            (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
        32)
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))))

noncomputable def p3771 :=
@p3764
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      32)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  p3770

noncomputable def p3772 :=
p3771
  (@Mathlib.Tactic.Ring.Common.zero_mul Real Real.instCommSemiring
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      (@Nat.rawCast Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne Real
          (@NonAssocSemiring.toAddCommMonoidWithOne Real
            (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
        32)
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))))

noncomputable def p3773 :=
p3772
  (@Mathlib.Tactic.Ring.Common.add_pf_add_zero Real Real.instCommSemiring
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      (@Nat.rawCast Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne Real
          (@NonAssocSemiring.toAddCommMonoidWithOne Real
            (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
        32)
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))))

noncomputable def p3777 :=
@HMul.hMul Real Real Real
  (@instHMul Real
    (@Distrib.toMul Real
      (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
  (@HPow.hPow Real Nat Real
    (@instHPow Real Nat
      (@NPow.toPow Real
        (@Monoid.toNPow Real
          (@Semiring.toMonoid Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
    Real.pi
    (@Nat.rawCast Nat
      (@AddCommMonoidWithOne.toAddMonoidWithOne Nat
        (@NonAssocSemiring.toAddCommMonoidWithOne Nat
          (@Semiring.toNonAssocSemiring Nat (@CommSemiring.toSemiring Nat Nat.instCommSemiring))))
      1))
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    1)

noncomputable def p3781 :=
fun (_a : Real) =>
  @Eq Real p3777
    (@HMul.hMul Real Real Real
      (@instHMul Real
        (@Distrib.toMul Real
          (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      (@HPow.hPow Real Nat Real
        (@instHPow Real Nat
          (@NPow.toPow Real
            (@Monoid.toNPow Real
              (@Semiring.toMonoid Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
        Real.pi
        (@Nat.rawCast Nat
          (@AddCommMonoidWithOne.toAddMonoidWithOne Nat
            (@NonAssocSemiring.toAddCommMonoidWithOne Nat
              (@Semiring.toNonAssocSemiring Nat (@CommSemiring.toSemiring Nat Nat.instCommSemiring))))
          1))
      _a)

noncomputable def p3782 :=
@congrArg Real Prop
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    1)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    1)
  p3781
  (@Eq.symm Real
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      1)
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      1)
    (@rfl Real
      (@Nat.rawCast Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne Real
          (@NonAssocSemiring.toAddCommMonoidWithOne Real
            (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
        1)))

noncomputable def p3819 :=
@HMul.hMul Real Real Real
  (@instHMul Real
    (@Distrib.toMul Real
      (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
  (@HPow.hPow Real Nat Real
    (@instHPow Real Nat
      (@NPow.toPow Real
        (@Monoid.toNPow Real
          (@Semiring.toMonoid Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
    Real.pi
    (@Nat.rawCast Nat
      (@AddCommMonoidWithOne.toAddMonoidWithOne Nat
        (@NonAssocSemiring.toAddCommMonoidWithOne Nat
          (@Semiring.toNonAssocSemiring Nat (@CommSemiring.toSemiring Nat Nat.instCommSemiring))))
      1))
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    20)

noncomputable def p3824 :=
@Mathlib.Tactic.Ring.Common.sub_congr Real Real.commRing (p3710 Real.pi)
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    p3819
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  p3712
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      63)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))

noncomputable def p3825 :=
@Mathlib.Tactic.Ring.Common.mul_congr Real Real.instCommSemiring
  (@OfNat.ofNat Real 20
    (@instOfNatAtLeastTwo Real 20
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3826 :=
@p3825
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      20)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  Real.pi

noncomputable def p3827 :=
@Mathlib.Tactic.Ring.cast_pos Real Real.instCommSemiring
  (@OfNat.ofNat Real 20
    (@instOfNatAtLeastTwo Real 20
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3828 :=
@Mathlib.Meta.NormNum.isNat_ofNat Real
  (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing))
  (@OfNat.ofNat Real 20
    (@instOfNatAtLeastTwo Real 20
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3829 :=
@p3826
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    p3777
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    p3819
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (@p3827 20
    (@p3828 20
      (@Eq.refl Real
        (@OfNat.ofNat Real 20
          (@instOfNatAtLeastTwo Real 20
            (@AddMonoidWithOne.toNatCast Real
              (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 18))))))

noncomputable def p3830 :=
p3829
  (@Mathlib.Tactic.Ring.Common.atom_pf Real Real.instCommSemiring p3777 Real.pi
    (@Nat.rawCast Nat
      (@AddCommMonoidWithOne.toAddMonoidWithOne Nat
        (@NonAssocSemiring.toAddCommMonoidWithOne Nat
          (@Semiring.toNonAssocSemiring Nat (@CommSemiring.toSemiring Nat Nat.instCommSemiring))))
      1)
    (@rfl Nat
      (@Nat.rawCast Nat
        (@AddCommMonoidWithOne.toAddMonoidWithOne Nat
          (@NonAssocSemiring.toAddCommMonoidWithOne Nat
            (@Semiring.toNonAssocSemiring Nat (@CommSemiring.toSemiring Nat Nat.instCommSemiring))))
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
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    20)
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    p3777
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    p3819
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))

noncomputable def p3832 :=
@Mathlib.Tactic.Ring.Common.mul_add Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    20)
  p3777
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  p3819

noncomputable def p3833 :=
@Mathlib.Tactic.Ring.Common.mul_pf_right Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    20)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    1)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    20)
  Real.pi

noncomputable def p3834 :=
@Mathlib.Meta.NormNum.IsNat.to_raw_eq Real
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      20)
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      1))
  20

noncomputable def p3835 :=
@Mathlib.Meta.NormNum.isNat_mul Real (@CommSemiring.toSemiring Real Real.instCommSemiring)
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    20)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    1)
  20 1

noncomputable def p3836 :=
@p3835 20
  (@Eq.refl (Real → Real → Real)
    (@HMul.hMul Real Real Real
      (@instHMul Real
        (@Distrib.toMul Real
          (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (@Mathlib.Meta.NormNum.IsNat.of_raw Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    20)
  (@Mathlib.Meta.NormNum.IsNat.of_raw Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    1)
  (@Eq.refl Nat 20)

noncomputable def p3837 :=
@p3832
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    p3819
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (p3833
    (@Nat.rawCast Nat
      (@AddCommMonoidWithOne.toAddMonoidWithOne Nat
        (@NonAssocSemiring.toAddCommMonoidWithOne Nat
          (@Semiring.toNonAssocSemiring Nat (@CommSemiring.toSemiring Nat Nat.instCommSemiring))))
      1)
    (@p3834
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      p3836))
  (@Mathlib.Tactic.Ring.Common.mul_zero Real Real.instCommSemiring
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      20))

noncomputable def p3838 :=
@p3831
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    p3819
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (p3837
    (@Mathlib.Tactic.Ring.Common.add_pf_add_zero Real Real.instCommSemiring
      (@HAdd.hAdd Real Real Real
        (@instHAdd Real
          (@Distrib.toAdd Real
            (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
        p3819
        (@OfNat.ofNat Real 0
          (@Zero.toOfNat0 Real
            (@MulZeroClass.toZero Real
              (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))))

noncomputable def p3839 :=
p3838
  (@Mathlib.Tactic.Ring.Common.zero_mul Real Real.instCommSemiring
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      p3777
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))))
  (@Mathlib.Tactic.Ring.Common.add_pf_add_zero Real Real.instCommSemiring
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      p3819
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))))

noncomputable def p3840 :=
@p3824
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 63))
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      p3819
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))))
  (p3830 p3839)

noncomputable def p3841 :=
@p3744 p3711
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      63)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      63)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))

noncomputable def p3842 :=
p3841
  (p3746
    (p3747
      (@Nat.cast_one Real
        (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing)))))
  (@Mathlib.Tactic.Ring.cast_pos Real Real.instCommSemiring p3711 63
    (@Mathlib.Meta.NormNum.isNat_ofNat Real
      (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing))
      p3711 63
      (@Eq.refl Real
        (@OfNat.ofNat Real 63
          (@instOfNatAtLeastTwo Real 63
            (@AddMonoidWithOne.toNatCast Real
              (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 61))))))

noncomputable def p3843 :=
@Mathlib.Tactic.Ring.Common.add_mul Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    1)
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      63)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      63)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))

noncomputable def p3844 :=
@Mathlib.Tactic.Ring.Common.mul_add Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    1)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    63)
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    63)

noncomputable def p3845 :=
@Mathlib.Meta.NormNum.IsNat.to_raw_eq Real
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      1)
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      63))
  63

noncomputable def p3846 :=
@Mathlib.Meta.NormNum.isNat_mul Real (@CommSemiring.toSemiring Real Real.instCommSemiring)
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    1)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    63)
  1 63

noncomputable def p3847 :=
@p3846 63
  (@Eq.refl (Real → Real → Real)
    (@HMul.hMul Real Real Real
      (@instHMul Real
        (@Distrib.toMul Real
          (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (@Mathlib.Meta.NormNum.IsNat.of_raw Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    1)
  (@Mathlib.Meta.NormNum.IsNat.of_raw Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    63)
  (@Eq.refl Nat 63)

noncomputable def p3848 :=
@p3844
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      63)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (@p3845
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    p3847)

noncomputable def p3849 :=
p3848
  (@Mathlib.Tactic.Ring.Common.mul_zero Real Real.instCommSemiring
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      1))
  (@Mathlib.Tactic.Ring.Common.add_pf_add_zero Real Real.instCommSemiring
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      (@Nat.rawCast Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne Real
          (@NonAssocSemiring.toAddCommMonoidWithOne Real
            (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
        63)
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))))

noncomputable def p3850 :=
@p3843
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      63)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  p3849

noncomputable def p3851 :=
p3850
  (@Mathlib.Tactic.Ring.Common.zero_mul Real Real.instCommSemiring
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      (@Nat.rawCast Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne Real
          (@NonAssocSemiring.toAddCommMonoidWithOne Real
            (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
        63)
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))))

noncomputable def p3852 :=
p3851
  (@Mathlib.Tactic.Ring.Common.add_pf_add_zero Real Real.instCommSemiring
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      (@Nat.rawCast Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne Real
          (@NonAssocSemiring.toAddCommMonoidWithOne Real
            (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
        63)
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))))

noncomputable def p3853 :=
@Mathlib.Tactic.Ring.Common.sub_pf Real Real.commRing
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    p3819
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      63)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 63))
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))

noncomputable def p3854 :=
@Mathlib.Tactic.Ring.Common.neg_add Real Real.commRing
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    63)
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (Int.negOfNat 63))
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))

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
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    63)

noncomputable def p3856 :=
@p3730
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    63)
  (Int.ofNat 63) (Int.negOfNat 63) p3731

noncomputable def p3857 :=
p3856
  (@Mathlib.Meta.NormNum.IsNat.to_isInt Real
    (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      63)
    63
    (@Mathlib.Meta.NormNum.IsNat.of_raw Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      63))

noncomputable def p3858 :=
@p3853
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 63))
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      p3819
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))))
  (p3854
    (@Mathlib.Meta.NormNum.IsInt.to_raw_eq Real p3855 (Int.negOfNat 63)
      (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (p3857 (@Eq.refl Int (Int.negOfNat 63))))
    (@Mathlib.Tactic.Ring.Common.neg_zero Real Real.commRing))

noncomputable def p3859 :=
@Mathlib.Tactic.Ring.Common.add_pf_add_gt Real Real.instCommSemiring
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    p3819
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    p3819
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))

noncomputable def p3860 :=
p3858
  (p3859
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 63))
    (@Mathlib.Tactic.Ring.Common.add_pf_add_zero Real Real.instCommSemiring
      (@HAdd.hAdd Real Real Real
        (@instHAdd Real
          (@Distrib.toAdd Real
            (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
        p3819
        (@OfNat.ofNat Real 0
          (@Zero.toOfNat0 Real
            (@MulZeroClass.toZero Real
              (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))))

noncomputable def p3930 :=
@HMul.hMul Real Real Real
  (@instHMul Real
    (@inferInstance (Mul Real)
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real
          (@DivisionSemiring.toSemiring Real
            (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField)))))))
  (@OfNat.ofNat Real 1
    (@One.toOfNat1 Real
      (@AddMonoidWithOne.toOne Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))))
  (@OfNat.ofNat Real 32
    (@instOfNatAtLeastTwo Real 32 Real.instNatCast
      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 31 (instOfNatNat 31))
        (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 30 (instOfNatNat 30))))))

noncomputable def p3938 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  (@OfNat.ofNat Real 20
    (@instOfNatAtLeastTwo Real 20
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3939 :=
@LT.lt Real (@Preorder.toLT Real (@PartialOrder.toPreorder Real Real.partialOrder))
  (p3938
    (@HSub.hSub Real Real Real
      (@instHSub Real
        (@SubNegMonoid.toSub Real
          (@AddGroup.toSubNegMonoid Real
            (@AddGroupWithOne.toAddGroup Real (@Ring.toAddGroupWithOne Real Real.instRing)))))
      Real.pi
      (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 315
        true 2)))

noncomputable def p3940 :=
@congrArg Real Prop
  (p3938
    (@HSub.hSub Real Real Real
      (@instHSub Real
        (@SubNegMonoid.toSub Real
          (@AddGroup.toSubNegMonoid Real
            (@AddGroupWithOne.toAddGroup Real (@Ring.toAddGroupWithOne Real Real.instRing)))))
      Real.pi
      (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 315
        true 2)))

noncomputable def p3941 :=
@OfNat.ofNat Real 20
  (@instOfNatAtLeastTwo Real 20
    (@AddMonoidWithOne.toNatCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real
            (@DivisionSemiring.toSemiring Real
              (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField)))))))
    (Mathlib.Meta.NormNum.instAtLeastTwo 18))

noncomputable def p3942 :=
@HSub.hSub Real Real Real
  (@instHSub Real
    (@SubNegMonoid.toSub Real
      (@AddGroup.toSubNegMonoid Real
        (@AddGroupWithOne.toAddGroup Real (@Ring.toAddGroupWithOne Real Real.instRing)))))
  Real.pi
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField))))))
    p3711 p3941)

noncomputable def p3943 :=
@Mathlib.Tactic.CancelDenoms.derive_trans Real Real.instMul
  (@HSub.hSub Real Real Real
    (@instHSub Real
      (@SubNegMonoid.toSub Real
        (@AddGroup.toSubNegMonoid Real
          (@AddGroupWithOne.toAddGroup Real (@Ring.toAddGroupWithOne Real Real.instRing)))))
    Real.pi
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 315 true
      2))
  p3942

noncomputable def p3944 :=
@p3943
  (@OfNat.ofNat Real 20
    (@instOfNatAtLeastTwo Real 20
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3945 :=
@Eq.trans Real
  (@HSub.hSub Real Real Real
    (@instHSub Real
      (@SubNegMonoid.toSub Real
        (@AddGroup.toSubNegMonoid Real
          (@AddGroupWithOne.toAddGroup Real (@Ring.toAddGroupWithOne Real Real.instRing)))))
    Real.pi
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 315 true
      2))
  p3942

noncomputable def p3946 :=
@congrArg Real Real
  (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 315 true
    2)
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField))))))
    p3711 p3941)

noncomputable def p3947 :=
@Mathlib.Meta.NormNum.isNNRat_nnratCast Real
  (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField))
  (@FloorSemiring.instCharZero Real Real.semiring Real.partialOrder
    (@FloorRing.toFloorSemiring Real Real.instRing Real.linearOrder Real.instFloorRing))
  (NNRat.divNat 315
    (@HPow.hPow Nat Nat Nat
      (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
      (@OfNat.ofNat Nat 10 (instOfNatNat 10)) 2))
  63 20

noncomputable def p3948 :=
@Mathlib.Meta.NormNum.isNNRat_divNat 315 315 63
  (@HPow.hPow Nat Nat Nat
    (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
    (@OfNat.ofNat Nat 10 (instOfNatNat 10)) 2)
  100 20 (Mathlib.Meta.NormNum.IsNat.raw_refl 315)

noncomputable def p3949 :=
@Mathlib.Meta.NormNum.isNat_pow Nat Nat.instSemiring
  (@HPow.hPow Nat Nat Nat
    (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))))
  (@OfNat.ofNat Nat 10 (instOfNatNat 10)) 2 10 2 100

noncomputable def p3950 :=
p3948
  (p3949
    (@Eq.refl (Nat → Nat → Nat)
      (@HPow.hPow Nat Nat Nat
        (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))))
    (@Mathlib.Meta.NormNum.isNat_ofNat Nat Nat.instAddMonoidWithOne
      (@OfNat.ofNat Nat 10 (instOfNatNat 10)) 10
      (@Eq.refl Nat (@OfNat.ofNat Nat 10 (instOfNatNat 10))))
    (Mathlib.Meta.NormNum.IsNat.raw_refl 2)
    (@Mathlib.Meta.NormNum.IsNatPowT.run 10 2 100
      (@Mathlib.Meta.NormNum.IsNatPowT.bit0 10 1 10)))

noncomputable def p3951 :=
@Mathlib.Meta.NormNum.isNNRat_div NNRat (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield)
  (@Nat.cast NNRat
    (@AddMonoidWithOne.toNatCast NNRat
      (@AddCommMonoidWithOne.toAddMonoidWithOne NNRat
        (@NonAssocSemiring.toAddCommMonoidWithOne NNRat
          (@Semiring.toNonAssocSemiring NNRat
            (@DivisionSemiring.toSemiring NNRat (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield))))))
    315)
  (@Nat.cast NNRat
    (@AddMonoidWithOne.toNatCast NNRat
      (@AddCommMonoidWithOne.toAddMonoidWithOne NNRat
        (@NonAssocSemiring.toAddCommMonoidWithOne NNRat
          (@Semiring.toNonAssocSemiring NNRat
            (@DivisionSemiring.toSemiring NNRat (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield))))))
    100)

noncomputable def p3952 :=
@Mathlib.Meta.NormNum.isNNRat_mul NNRat
  (@DivisionSemiring.toSemiring NNRat (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield))
  (@HMul.hMul NNRat NNRat NNRat
    (@instHMul NNRat
      (@Distrib.toMul NNRat
        (@instDistribOfSemiring NNRat
          (@DivisionSemiring.toSemiring NNRat (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield))))))
  (@Nat.cast NNRat
    (@AddMonoidWithOne.toNatCast NNRat
      (@AddCommMonoidWithOne.toAddMonoidWithOne NNRat
        (@NonAssocSemiring.toAddCommMonoidWithOne NNRat
          (@Semiring.toNonAssocSemiring NNRat
            (@DivisionSemiring.toSemiring NNRat (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield))))))
    315)
  (@Inv.inv NNRat
    (@InvOneClass.toInv NNRat
      (@DivInvOneMonoid.toInvOneClass NNRat
        (@DivisionMonoid.toDivInvOneMonoid NNRat
          (@GroupWithZero.toDivisionMonoid NNRat
            (@DivisionSemiring.toGroupWithZero NNRat
              (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield))))))
    (@Nat.cast NNRat
      (@AddMonoidWithOne.toNatCast NNRat
        (@AddCommMonoidWithOne.toAddMonoidWithOne NNRat
          (@NonAssocSemiring.toAddCommMonoidWithOne NNRat
            (@Semiring.toNonAssocSemiring NNRat
              (@DivisionSemiring.toSemiring NNRat (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield))))))
      100))

noncomputable def p3953 :=
@Mathlib.Meta.NormNum.IsNat.to_isNNRat NNRat
  (@DivisionSemiring.toSemiring NNRat (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield))
  (@Nat.cast NNRat
    (@AddMonoidWithOne.toNatCast NNRat
      (@AddCommMonoidWithOne.toAddMonoidWithOne NNRat
        (@NonAssocSemiring.toAddCommMonoidWithOne NNRat
          (@Semiring.toNonAssocSemiring NNRat
            (@DivisionSemiring.toSemiring NNRat (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield))))))
    315)
  315

noncomputable def p3954 :=
p3953
  (@Mathlib.Meta.NormNum.isNat_natCast NNRat
    (@AddCommMonoidWithOne.toAddMonoidWithOne NNRat
      (@NonAssocSemiring.toAddCommMonoidWithOne NNRat
        (@Semiring.toNonAssocSemiring NNRat
          (@DivisionSemiring.toSemiring NNRat (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield)))))
    315 315 (Mathlib.Meta.NormNum.IsNat.raw_refl 315))

noncomputable def p3955 :=
@Mathlib.Meta.NormNum.isNNRat_inv_pos NNRat (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield)
  NNRat.instCharZero
  (@Nat.cast NNRat
    (@AddMonoidWithOne.toNatCast NNRat
      (@AddCommMonoidWithOne.toAddMonoidWithOne NNRat
        (@NonAssocSemiring.toAddCommMonoidWithOne NNRat
          (@Semiring.toNonAssocSemiring NNRat
            (@DivisionSemiring.toSemiring NNRat (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield))))))
    100)
  99

noncomputable def p3956 :=
@Mathlib.Meta.NormNum.IsNat.to_isNNRat NNRat
  (@DivisionSemiring.toSemiring NNRat (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield))
  (@Nat.cast NNRat
    (@AddMonoidWithOne.toNatCast NNRat
      (@AddCommMonoidWithOne.toAddMonoidWithOne NNRat
        (@NonAssocSemiring.toAddCommMonoidWithOne NNRat
          (@Semiring.toNonAssocSemiring NNRat
            (@DivisionSemiring.toSemiring NNRat (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield))))))
    100)
  100

noncomputable def p3957 :=
p3956
  (@Mathlib.Meta.NormNum.isNat_natCast NNRat
    (@AddCommMonoidWithOne.toAddMonoidWithOne NNRat
      (@NonAssocSemiring.toAddCommMonoidWithOne NNRat
        (@Semiring.toNonAssocSemiring NNRat
          (@DivisionSemiring.toSemiring NNRat (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield)))))
    100 100 (Mathlib.Meta.NormNum.IsNat.raw_refl 100))

noncomputable def p3958 :=
@p3952 315 1 63 1 100 20 5
  (@Eq.refl (NNRat → NNRat → NNRat)
    (@HMul.hMul NNRat NNRat NNRat
      (@instHMul NNRat
        (@Distrib.toMul NNRat
          (@instDistribOfSemiring NNRat
            (@DivisionSemiring.toSemiring NNRat (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield)))))))
  p3954 (@p3955 1 p3957)

noncomputable def p3959 :=
@Mathlib.Meta.NormNum.IsNNRat.to_eq Real
  (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField)) 63 20
  (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 315 true
    2)
  p3711 p3941
  (@Mathlib.Meta.NormNum.isNNRat_ofScientific_of_true Real
    (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField)) 315 2
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
      (@instHSub Real
        (@SubNegMonoid.toSub Real
          (@AddGroup.toSubNegMonoid Real
            (@AddGroupWithOne.toAddGroup Real (@Ring.toAddGroupWithOne Real Real.instRing)))))
      Real.pi)
    (p3959 (@Eq.refl Real p3941)))

noncomputable def p3961 :=
@congrArg Real Real
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField))))))
    p3711 p3941)

noncomputable def p3962 :=
@p3961
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField))))))
    p3711 p3941)

noncomputable def p3963 :=
@Mathlib.Meta.NormNum.IsNNRat.to_eq Real
  (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField)) 63 20
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField))))))
    p3711 p3941)

noncomputable def p3964 :=
@Mathlib.Meta.NormNum.isNNRat_mul Real
  (@DivisionSemiring.toSemiring Real
    (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField)))
  (@HMul.hMul Real Real Real
    (@instHMul Real (@Distrib.toMul Real (@instDistribOfSemiring Real Real.semiring))))
  p3711
  (@Inv.inv Real
    (@InvOneClass.toInv Real
      (@DivInvOneMonoid.toInvOneClass Real
        (@DivisionMonoid.toDivInvOneMonoid Real
          (@GroupWithZero.toDivisionMonoid Real
            (@DivisionSemiring.toGroupWithZero Real
              (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField)))))))
    p3941)

noncomputable def p3965 :=
@p3964 63 1 63 1 20 20 1
  (@Eq.refl (Real → Real → Real)
    (@HMul.hMul Real Real Real
      (@instHMul Real (@Distrib.toMul Real (@instDistribOfSemiring Real Real.semiring)))))
  (@Mathlib.Meta.NormNum.IsNat.to_isNNRat Real
    (@DivisionSemiring.toSemiring Real
      (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField)))
    p3711 63
    (@Mathlib.Meta.NormNum.isNat_ofNat Real
      (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing))
      p3711 63
      (@Eq.refl Real
        (@OfNat.ofNat Real 63
          (@instOfNatAtLeastTwo Real 63
            (@AddMonoidWithOne.toNatCast Real
              (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 61))))))

noncomputable def p3966 :=
@Mathlib.Meta.NormNum.isNNRat_inv_pos Real
  (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField))
  (@FloorSemiring.instCharZero Real Real.semiring Real.partialOrder
    (@FloorRing.toFloorSemiring Real Real.instRing Real.linearOrder Real.instFloorRing))
  p3941 19 1
  (@Mathlib.Meta.NormNum.IsNat.to_isNNRat Real
    (@DivisionSemiring.toSemiring Real
      (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField)))
    p3941 20
    (@Mathlib.Meta.NormNum.isNat_ofNat Real
      (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing))
      p3941 20
      (@Eq.refl Real
        (@OfNat.ofNat Real 20
          (@instOfNatAtLeastTwo Real 20
            (@AddMonoidWithOne.toNatCast Real
              (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 18))))))

noncomputable def p3967 :=
@p3963 p3711 p3941
  (@Mathlib.Meta.NormNum.isNNRat_div Real
    (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField)) p3711
    p3941 63 20
    (p3965 p3966 (@Eq.refl Nat (Nat.mul 63 1))
      (@Eq.refl Nat 20)))
  (@Eq.refl Real p3711)

noncomputable def p3968 :=
p3960
  (p3962
    (@HSub.hSub Real Real Real
      (@instHSub Real
        (@SubNegMonoid.toSub Real
          (@AddGroup.toSubNegMonoid Real
            (@AddGroupWithOne.toAddGroup Real (@Ring.toAddGroupWithOne Real Real.instRing)))))
      Real.pi)
    (p3967 (@Eq.refl Real p3941)))

noncomputable def p3969 :=
@Mathlib.Tactic.CancelDenoms.sub_subst Real
  (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))
  (@OfNat.ofNat Real 20
    (@instOfNatAtLeastTwo Real 20
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3970 :=
@p3969 Real.pi
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField))))))
    p3711 p3941)

noncomputable def p3971 :=
@HMul.hMul Real Real Real
  (@instHMul Real
    (@inferInstance (Mul Real)
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real
          (@DivisionSemiring.toSemiring Real
            (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField)))))))
  (@OfNat.ofNat Real 20
    (@instOfNatAtLeastTwo Real 20
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3972 :=
@Mathlib.Tactic.CancelDenoms.div_subst Real Real.instField
  (@OfNat.ofNat Real 1
    (@One.toOfNat1 Real
      (@AddMonoidWithOne.toOne Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))))
  (@OfNat.ofNat Real 20
    (@instOfNatAtLeastTwo Real 20
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3973 :=
@p3972
  (@OfNat.ofNat Real 20
    (@instOfNatAtLeastTwo Real 20
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3974 :=
@HMul.hMul Real Real Real
  (@instHMul Real
    (@inferInstance (Mul Real)
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real
          (@DivisionSemiring.toSemiring Real
            (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField)))))))
  (@OfNat.ofNat Real 1
    (@One.toOfNat1 Real
      (@AddMonoidWithOne.toOne Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))))
  p3711

noncomputable def p3975 :=
@HDiv.hDiv Real Real Real
  (@instHDiv Real
    (@DivInvMonoid.toDiv Real
      (@DivisionRing.toDivInvMonoid Real (@Field.toDivisionRing Real Real.instField))))
  (@OfNat.ofNat Real 20
    (@instOfNatAtLeastTwo Real 20
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3976 :=
@Mathlib.Meta.NormNum.isNat_eq_true Real
  (@Mathlib.Meta.NormNum.instAddMonoidWithOne' Real
    (@DivisionSemiring.toSemiring Real
      (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField))))
  (p3975 p3941)
  (@OfNat.ofNat Real 1
    (@One.toOfNat1 Real
      (@AddMonoidWithOne.toOne Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))))
  1

noncomputable def p3977 :=
@Mathlib.Meta.NormNum.isNNRat_div Real
  (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField))
  (@OfNat.ofNat Real 20
    (@instOfNatAtLeastTwo Real 20
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3978 :=
p3710
  (@Inv.inv Real
    (@InvOneClass.toInv Real
      (@DivInvOneMonoid.toInvOneClass Real
        (@DivisionMonoid.toDivInvOneMonoid Real
          (@GroupWithZero.toDivisionMonoid Real
            (@DivisionSemiring.toGroupWithZero Real
              (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField)))))))
    p3941)

noncomputable def p3979 :=
@HMul.hMul Real Real Real
  (@instHMul Real (@Distrib.toMul Real (@instDistribOfSemiring Real Real.semiring)))
  (@OfNat.ofNat Real 20
    (@instOfNatAtLeastTwo Real 20
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3980 :=
p3979
  (@Inv.inv Real
    (@InvOneClass.toInv Real
      (@DivInvOneMonoid.toInvOneClass Real
        (@DivisionMonoid.toDivInvOneMonoid Real
          (@GroupWithZero.toDivisionMonoid Real
            (@DivisionSemiring.toGroupWithZero Real
              (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField)))))))
    p3941)

noncomputable def p3981 :=
@Mathlib.Meta.NormNum.isNNRat_mul Real
  (@DivisionSemiring.toSemiring Real
    (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField)))
  (@HMul.hMul Real Real Real
    (@instHMul Real (@Distrib.toMul Real (@instDistribOfSemiring Real Real.semiring))))
  (@OfNat.ofNat Real 20
    (@instOfNatAtLeastTwo Real 20
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3982 :=
@p3981
  (@Inv.inv Real
    (@InvOneClass.toInv Real
      (@DivInvOneMonoid.toInvOneClass Real
        (@DivisionMonoid.toDivInvOneMonoid Real
          (@GroupWithZero.toDivisionMonoid Real
            (@DivisionSemiring.toGroupWithZero Real
              (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField)))))))
    p3941)

noncomputable def p3983 :=
@Mathlib.Meta.NormNum.IsNat.to_isNNRat Real
  (@DivisionSemiring.toSemiring Real
    (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField)))
  (@OfNat.ofNat Real 20
    (@instOfNatAtLeastTwo Real 20
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3984 :=
@p3982 20 1 1 1 20 1 20
  (@Eq.refl (Real → Real → Real)
    (@HMul.hMul Real Real Real
      (@instHMul Real (@Distrib.toMul Real (@instDistribOfSemiring Real Real.semiring)))))
  (@p3983 20
    (@p3828 20
      (@Eq.refl Real
        (@OfNat.ofNat Real 20
          (@instOfNatAtLeastTwo Real 20
            (@AddMonoidWithOne.toNatCast Real
              (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 18))))))

noncomputable def p3985 :=
@Mathlib.Meta.NormNum.IsNNRat.to_isNat Real
  (@DivisionSemiring.toSemiring Real
    (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField)))
  (p3975 p3941) 1
  (@p3977 p3941 1 1
    (@Mathlib.Meta.NormNum.IsNat.to_isNNRat Real
      (@DivisionSemiring.toSemiring Real
        (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField)))
      p3978 1
      (@Mathlib.Meta.NormNum.IsNNRat.to_isNat Real
        (@DivisionSemiring.toSemiring Real
          (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField)))
        p3980 1
        (p3984 p3966 (@Eq.refl Nat (Nat.mul 20 1))
          (@Eq.refl Nat 20)))))

noncomputable def p3986 :=
@HMul.hMul Real Real Real
  (@instHMul Real
    (@Distrib.toMul Real
      (@instDistribOfSemiring Real
        (@DivisionSemiring.toSemiring Real
          (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField))))))
  (@OfNat.ofNat Real 1
    (@One.toOfNat1 Real
      (@AddMonoidWithOne.toOne Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))))
  (@OfNat.ofNat Real 20
    (@instOfNatAtLeastTwo Real 20
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3987 :=
@Mathlib.Meta.NormNum.isNat_eq_true Real
  (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing))
  p3986
  (@OfNat.ofNat Real 20
    (@instOfNatAtLeastTwo Real 20
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3988 :=
@Mathlib.Meta.NormNum.isNat_mul Real Real.semiring
  (@HMul.hMul Real Real Real
    (@instHMul Real (@Distrib.toMul Real (@instDistribOfSemiring Real Real.semiring))))
  (@OfNat.ofNat Real 1
    (@One.toOfNat1 Real
      (@AddMonoidWithOne.toOne Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))))
  (@OfNat.ofNat Real 20
    (@instOfNatAtLeastTwo Real 20
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3989 :=
@p3988 1 20 20
  (@Eq.refl (Real → Real → Real)
    (@HMul.hMul Real Real Real
      (@instHMul Real (@Distrib.toMul Real (@instDistribOfSemiring Real Real.semiring)))))
  (p3747
    (@Nat.cast_one Real
      (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing))))
  (@p3828 20
    (@Eq.refl Real
      (@OfNat.ofNat Real 20
        (@instOfNatAtLeastTwo Real 20
          (@AddMonoidWithOne.toNatCast Real
            (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing)))
          (Mathlib.Meta.NormNum.instAtLeastTwo 18)))))
  (@Eq.refl Nat 20)

noncomputable def p3990 :=
@p3973 p3711 p3941 p3712
  (@rfl Real p3974)
  (p3976 p3985
    (p3747
      (@Nat.cast_one Real
        (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing)))))
  (@p3987 20 p3989
    (@p3828 20
      (@Eq.refl Real
        (@OfNat.ofNat Real 20
          (@instOfNatAtLeastTwo Real 20
            (@AddMonoidWithOne.toNatCast Real
              (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 18))))))

noncomputable def p3991 :=
@Eq.mp
  (p3939
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@Ring.toSemiring Real Real.instRing))))))
  (@LT.lt Real (@Preorder.toLT Real (@PartialOrder.toPreorder Real Real.partialOrder))
    p3713
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@Ring.toSemiring Real Real.instRing))))))
  (@p3940 p3713
    (fun (_a : Real) =>
      @LT.lt Real (@Preorder.toLT Real (@PartialOrder.toPreorder Real Real.partialOrder)) _a
        (@OfNat.ofNat Real 0
          (@Zero.toOfNat0 Real
            (@MulZeroClass.toZero Real
              (@instMulZeroClassOfSemiring Real (@Ring.toSemiring Real Real.instRing))))))
    (@p3944 p3713 p3968
      (@p3970 (p3710 Real.pi) p3712
        (@rfl Real (p3971 Real.pi)) p3990)))

noncomputable def p3992 :=
@Mathlib.Tactic.Linarith.mul_neg Real Real.instRing Real.partialOrder Real.instIsStrictOrderedRing
  (@HSub.hSub Real Real Real
    (@instHSub Real
      (@SubNegMonoid.toSub Real
        (@AddGroup.toSubNegMonoid Real
          (@AddGroupWithOne.toAddGroup Real (@Ring.toAddGroupWithOne Real Real.instRing)))))
    Real.pi
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 315 true
      2))
  (@OfNat.ofNat Real 20
    (@instOfNatAtLeastTwo Real 20 Real.instNatCast
      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 19 (instOfNatNat 19))
        (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 18 (instOfNatNat 18))))))

noncomputable def p3993 :=
@Mathlib.Meta.NormNum.isNat_lt_true Real Real.semiring Real.partialOrder Real.instIsOrderedRing
  (@FloorSemiring.instCharZero Real (@Ring.toSemiring Real Real.instRing) Real.partialOrder
    (@FloorRing.toFloorSemiring Real Real.instRing Real.linearOrder Real.instFloorRing))
  (@OfNat.ofNat Real 0 (@Zero.toOfNat0 Real Real.instZero))
  (@OfNat.ofNat Real 20
    (@instOfNatAtLeastTwo Real 20 Real.instNatCast
      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 19 (instOfNatNat 19))
        (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 18 (instOfNatNat 18))))))
  0 20
  (@Mathlib.Meta.NormNum.isNat_ofNat Real
    (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing))
    (@OfNat.ofNat Real 0 (@Zero.toOfNat0 Real Real.instZero)) 0
    (@Nat.cast_zero Real
      (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing))))

noncomputable def p3994 :=
p3993
  (@Mathlib.Meta.NormNum.isNat_ofNat Real
    (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing))
    (@OfNat.ofNat Real 20
      (@instOfNatAtLeastTwo Real 20 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 19 (instOfNatNat 19))
          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 18 (instOfNatNat 18))))))
    20
    (@Eq.refl Real
      (@OfNat.ofNat Real 20
        (@instOfNatAtLeastTwo Real 20
          (@AddMonoidWithOne.toNatCast Real
            (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing)))
          (Mathlib.Meta.NormNum.instAtLeastTwo 18)))))

noncomputable def p3995 :=
p3991
  (p3992
    (@Mathlib.Tactic.Linarith.sub_neg_of_lt Real Real.instRing Real.partialOrder Real.instIsOrderedRing Real.pi
      (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 315
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
              (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField)))))))
    (Mathlib.Meta.NormNum.instAtLeastTwo 498))

noncomputable def p4091 :=
@Mathlib.Meta.NormNum.isNNRat_inv_pos Real
  (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField))
  (@FloorSemiring.instCharZero Real Real.semiring Real.partialOrder
    (@FloorRing.toFloorSemiring Real Real.instRing Real.linearOrder Real.instFloorRing))
  p4068 499 1
  (@Mathlib.Meta.NormNum.IsNat.to_isNNRat Real
    (@DivisionSemiring.toSemiring Real
      (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField)))
    p4068 500
    (@Mathlib.Meta.NormNum.isNat_ofNat Real
      (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing))
      p4068 500
      (@Eq.refl Real
        (@OfNat.ofNat Real 500
          (@instOfNatAtLeastTwo Real 500
            (@AddMonoidWithOne.toNatCast Real
              (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 498))))))

noncomputable def p5018 :=
nat_lit 73786976294838206464000000000000000

noncomputable def p5674 :=
nat_lit
  3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713438470702986642486608412251521024

noncomputable def p5940 :=
nat_lit 87112285931760246646623899502532662132736

noncomputable def p5990 :=
nat_lit 25711008708143844408671393477458601640355247900524685364822016000000000

noncomputable def p5994 :=
nat_lit 87112285931760246646623899502532662132736000000

noncomputable def p7287 :=
nat_lit
  12194330274671844653834364178879555881830461494785043558043581873536608354764709453594945715091765512343073949692994620685343654997219864477696

noncomputable def p8045 :=
nat_lit 2239744742177804210557442280568444278121645497234649534899989100963791871180160945380877493271607115776

noncomputable def p8250 :=
@HMul.hMul Real Real Real
  (@instHMul Real
    (@Distrib.toMul Real
      (@instDistribOfSemiring Real
        (@DivisionSemiring.toSemiring Real
          (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField))))))
  (@OfNat.ofNat Real 500
    (@instOfNatAtLeastTwo Real 500
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8253 :=
@HMul.hMul Real Real Real
  (@instHMul Real (@Distrib.toMul Real (@instDistribOfSemiring Real Real.semiring)))
  (@OfNat.ofNat Real 800
    (@instOfNatAtLeastTwo Real 800
      (@AddMonoidWithOne.toNatCast Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne Real
          (@NonAssocSemiring.toAddCommMonoidWithOne Real (@Semiring.toNonAssocSemiring Real Real.semiring))))
      (@Nat.instAtLeastTwoHAddOfNat
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) 798
          (@OfNat.ofNat Nat 1 (instOfNatNat 1)))
        (@instNeZeroNatHAdd_1 798 (@OfNat.ofNat Nat 1 (instOfNatNat 1))
          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 0 (instOfNatNat 0)))))))

noncomputable def p8255 :=
@HMul.hMul Real Real Real
  (@instHMul Real
    (@Distrib.toMul Real
      (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
  (@HPow.hPow Real Nat Real
    (@instHPow Real Nat
      (@NPow.toPow Real
        (@Monoid.toNPow Real
          (@Semiring.toMonoid Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
    Real.pi
    (@Nat.rawCast Nat
      (@AddCommMonoidWithOne.toAddMonoidWithOne Nat
        (@NonAssocSemiring.toAddCommMonoidWithOne Nat
          (@Semiring.toNonAssocSemiring Nat (@CommSemiring.toSemiring Nat Nat.instCommSemiring))))
      1))
  (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (Int.negOfNat 16000))

noncomputable def p8257 :=
@HMul.hMul Real Real Real
  (@instHMul Real
    (@Distrib.toMul Real
      (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
  (@HPow.hPow Real Nat Real
    (@instHPow Real Nat
      (@NPow.toPow Real
        (@Monoid.toNPow Real
          (@Semiring.toMonoid Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
    Real.pi
    (@Nat.rawCast Nat
      (@AddCommMonoidWithOne.toAddMonoidWithOne Nat
        (@NonAssocSemiring.toAddCommMonoidWithOne Nat
          (@Semiring.toNonAssocSemiring Nat (@CommSemiring.toSemiring Nat Nat.instCommSemiring))))
      1))
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    16000)

noncomputable def p8289 :=
@Mathlib.Tactic.Ring.Common.mul_congr Real Real.instCommSemiring p3705
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      32)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (p8250 Real.pi)

noncomputable def p8290 :=
@HMul.hMul Real Real Real
  (@instHMul Real
    (@Distrib.toMul Real
      (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
  (@HPow.hPow Real Nat Real
    (@instHPow Real Nat
      (@NPow.toPow Real
        (@Monoid.toNPow Real
          (@Semiring.toMonoid Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
    Real.pi
    (@Nat.rawCast Nat
      (@AddCommMonoidWithOne.toAddMonoidWithOne Nat
        (@NonAssocSemiring.toAddCommMonoidWithOne Nat
          (@Semiring.toNonAssocSemiring Nat (@CommSemiring.toSemiring Nat Nat.instCommSemiring))))
      1))
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    500)

noncomputable def p8291 :=
@p8289
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    p8290
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    p8257
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (p3762
    (p3746
      (p3747
        (@Nat.cast_one Real
          (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing)))))
    p3763 p3773)

noncomputable def p8292 :=
@Mathlib.Tactic.Ring.Common.mul_congr Real Real.instCommSemiring
  (@OfNat.ofNat Real 500
    (@instOfNatAtLeastTwo Real 500
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8293 :=
@p8292
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      500)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  Real.pi

noncomputable def p8294 :=
@Mathlib.Tactic.Ring.cast_pos Real Real.instCommSemiring
  (@OfNat.ofNat Real 500
    (@instOfNatAtLeastTwo Real 500
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8295 :=
@Mathlib.Meta.NormNum.isNat_ofNat Real
  (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing))
  (@OfNat.ofNat Real 500
    (@instOfNatAtLeastTwo Real 500
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8296 :=
@p8293
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    p3777
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    p8290
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (@p8294 500
    (@p8295 500
      (@Eq.refl Real
        (@OfNat.ofNat Real 500
          (@instOfNatAtLeastTwo Real 500
            (@AddMonoidWithOne.toNatCast Real
              (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 498))))))

noncomputable def p8297 :=
p8296
  (@Mathlib.Tactic.Ring.Common.atom_pf Real Real.instCommSemiring p3777 Real.pi
    (@Nat.rawCast Nat
      (@AddCommMonoidWithOne.toAddMonoidWithOne Nat
        (@NonAssocSemiring.toAddCommMonoidWithOne Nat
          (@Semiring.toNonAssocSemiring Nat (@CommSemiring.toSemiring Nat Nat.instCommSemiring))))
      1)
    (@rfl Nat
      (@Nat.rawCast Nat
        (@AddCommMonoidWithOne.toAddMonoidWithOne Nat
          (@NonAssocSemiring.toAddCommMonoidWithOne Nat
            (@Semiring.toNonAssocSemiring Nat (@CommSemiring.toSemiring Nat Nat.instCommSemiring))))
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
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    500)
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    p3777
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    p8290
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))

noncomputable def p8299 :=
@Mathlib.Tactic.Ring.Common.mul_add Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    500)
  p3777
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  p8290

noncomputable def p8300 :=
@Mathlib.Tactic.Ring.Common.mul_pf_right Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    500)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    1)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    500)
  Real.pi

noncomputable def p8301 :=
@Mathlib.Meta.NormNum.IsNat.to_raw_eq Real
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      500)
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      1))
  500

noncomputable def p8302 :=
@Mathlib.Meta.NormNum.isNat_mul Real (@CommSemiring.toSemiring Real Real.instCommSemiring)
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    500)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    1)
  500 1

noncomputable def p8303 :=
@p8302 500
  (@Eq.refl (Real → Real → Real)
    (@HMul.hMul Real Real Real
      (@instHMul Real
        (@Distrib.toMul Real
          (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (@Mathlib.Meta.NormNum.IsNat.of_raw Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    500)
  (@Mathlib.Meta.NormNum.IsNat.of_raw Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    1)
  (@Eq.refl Nat 500)

noncomputable def p8304 :=
@p8299
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    p8290
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (p8300
    (@Nat.rawCast Nat
      (@AddCommMonoidWithOne.toAddMonoidWithOne Nat
        (@NonAssocSemiring.toAddCommMonoidWithOne Nat
          (@Semiring.toNonAssocSemiring Nat (@CommSemiring.toSemiring Nat Nat.instCommSemiring))))
      1)
    (@p8301
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      p8303))
  (@Mathlib.Tactic.Ring.Common.mul_zero Real Real.instCommSemiring
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      500))

noncomputable def p8305 :=
@p8298
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    p8290
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (p8304
    (@Mathlib.Tactic.Ring.Common.add_pf_add_zero Real Real.instCommSemiring
      (@HAdd.hAdd Real Real Real
        (@instHAdd Real
          (@Distrib.toAdd Real
            (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
        p8290
        (@OfNat.ofNat Real 0
          (@Zero.toOfNat0 Real
            (@MulZeroClass.toZero Real
              (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))))

noncomputable def p8306 :=
p8305
  (@Mathlib.Tactic.Ring.Common.zero_mul Real Real.instCommSemiring
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      p3777
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))))
  (@Mathlib.Tactic.Ring.Common.add_pf_add_zero Real Real.instCommSemiring
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      p8290
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))))

noncomputable def p8307 :=
@Mathlib.Tactic.Ring.Common.add_mul Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    32)
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    p8290
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    p8257
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))

noncomputable def p8308 :=
@Mathlib.Tactic.Ring.Common.mul_add Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    32)
  p8290
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  p8257

noncomputable def p8309 :=
@Mathlib.Tactic.Ring.Common.mul_pf_right Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    32)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    500)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    16000)
  Real.pi

noncomputable def p8310 :=
@Mathlib.Meta.NormNum.IsNat.to_raw_eq Real
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      32)
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      500))
  16000

noncomputable def p8311 :=
@Mathlib.Meta.NormNum.isNat_mul Real (@CommSemiring.toSemiring Real Real.instCommSemiring)
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    32)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    500)
  32 500

noncomputable def p8312 :=
@p8311 16000
  (@Eq.refl (Real → Real → Real)
    (@HMul.hMul Real Real Real
      (@instHMul Real
        (@Distrib.toMul Real
          (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (@Mathlib.Meta.NormNum.IsNat.of_raw Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    32)
  (@Mathlib.Meta.NormNum.IsNat.of_raw Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    500)
  (@Eq.refl Nat 16000)

noncomputable def p8313 :=
@p8308
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    p8257
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (p8309
    (@Nat.rawCast Nat
      (@AddCommMonoidWithOne.toAddMonoidWithOne Nat
        (@NonAssocSemiring.toAddCommMonoidWithOne Nat
          (@Semiring.toNonAssocSemiring Nat (@CommSemiring.toSemiring Nat Nat.instCommSemiring))))
      1)
    (@p8310
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      p8312))
  (@Mathlib.Tactic.Ring.Common.mul_zero Real Real.instCommSemiring
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      32))

noncomputable def p8314 :=
@p8307
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    p8257
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (p8313
    (@Mathlib.Tactic.Ring.Common.add_pf_add_zero Real Real.instCommSemiring
      (@HAdd.hAdd Real Real Real
        (@instHAdd Real
          (@Distrib.toAdd Real
            (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
        p8257
        (@OfNat.ofNat Real 0
          (@Zero.toOfNat0 Real
            (@MulZeroClass.toZero Real
              (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))))

noncomputable def p8315 :=
p8314
  (@Mathlib.Tactic.Ring.Common.zero_mul Real Real.instCommSemiring
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      p8290
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))))
  (@Mathlib.Tactic.Ring.Common.add_pf_add_zero Real Real.instCommSemiring
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      p8257
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))))

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
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    16000)

noncomputable def p8318 :=
@p3730
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    16000)
  (Int.ofNat 16000) (Int.negOfNat 16000) p3731

noncomputable def p8319 :=
p8318
  (@Mathlib.Meta.NormNum.IsNat.to_isInt Real
    (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      16000)
    16000
    (@Mathlib.Meta.NormNum.IsNat.of_raw Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      16000))

noncomputable def p8320 :=
@Mathlib.Tactic.Ring.Common.neg_mul Real Real.commRing Real.pi
  (@Nat.rawCast Nat
    (@AddCommMonoidWithOne.toAddMonoidWithOne Nat
      (@NonAssocSemiring.toAddCommMonoidWithOne Nat
        (@Semiring.toNonAssocSemiring Nat (@CommSemiring.toSemiring Nat Nat.instCommSemiring))))
    1)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
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
        (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  p8255
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  p8320 (@Mathlib.Tactic.Ring.Common.neg_zero Real Real.commRing)

noncomputable def p8331 :=
@Mathlib.Tactic.Ring.Common.mul_congr Real Real.instCommSemiring
  (@OfNat.ofNat Real 800
    (@instOfNatAtLeastTwo Real 800
      (@AddMonoidWithOne.toNatCast Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne Real
          (@NonAssocSemiring.toAddCommMonoidWithOne Real (@Semiring.toNonAssocSemiring Real Real.semiring))))
      (@Nat.instAtLeastTwoHAddOfNat
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) 798
          (@OfNat.ofNat Nat 1 (instOfNatNat 1)))
        (@instNeZeroNatHAdd_1 798 (@OfNat.ofNat Nat 1 (instOfNatNat 1))
          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 0 (instOfNatNat 0)))))))

noncomputable def p8332 :=
@p8331
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      800)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  p3713

noncomputable def p8333 :=
@p8332
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 63))
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      p3819
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 50400))
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      p8257
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))))

noncomputable def p8334 :=
@Mathlib.Tactic.Ring.cast_pos Real Real.instCommSemiring
  (@OfNat.ofNat Real 800
    (@instOfNatAtLeastTwo Real 800
      (@AddMonoidWithOne.toNatCast Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne Real
          (@NonAssocSemiring.toAddCommMonoidWithOne Real (@Semiring.toNonAssocSemiring Real Real.semiring))))
      (@Nat.instAtLeastTwoHAddOfNat
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) 798
          (@OfNat.ofNat Nat 1 (instOfNatNat 1)))
        (@instNeZeroNatHAdd_1 798 (@OfNat.ofNat Nat 1 (instOfNatNat 1))
          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 0 (instOfNatNat 0)))))))

noncomputable def p8335 :=
@Mathlib.Meta.NormNum.isNat_ofNat Real
  (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing))
  (@OfNat.ofNat Real 800
    (@instOfNatAtLeastTwo Real 800
      (@AddMonoidWithOne.toNatCast Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne Real
          (@NonAssocSemiring.toAddCommMonoidWithOne Real (@Semiring.toNonAssocSemiring Real Real.semiring))))
      (@Nat.instAtLeastTwoHAddOfNat
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) 798
          (@OfNat.ofNat Nat 1 (instOfNatNat 1)))
        (@instNeZeroNatHAdd_1 798 (@OfNat.ofNat Nat 1 (instOfNatNat 1))
          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 0 (instOfNatNat 0)))))))

noncomputable def p8336 :=
p8333
  (@p8334 800
    (@p8335 800
      (@Eq.refl Real
        (@OfNat.ofNat Real 800
          (@instOfNatAtLeastTwo Real 800
            (@AddMonoidWithOne.toNatCast Real
              (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 798))))))

noncomputable def p8337 :=
@Mathlib.Tactic.Ring.Common.add_mul Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    800)
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 63))
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      p3819
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 50400))
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      p8257
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))))

noncomputable def p8338 :=
@Mathlib.Tactic.Ring.Common.mul_add Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    800)
  (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (Int.negOfNat 63))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    p3819
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (Int.negOfNat 50400))

noncomputable def p8339 :=
@Mathlib.Meta.NormNum.IsInt.to_raw_eq Real
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
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
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
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
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      800)
    800
    (@Mathlib.Meta.NormNum.IsNat.of_raw Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      800))

noncomputable def p8342 :=
@p8338
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    p8257
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 50400))
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      p8257
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))))
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
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    800)
  p3819
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  p8257

noncomputable def p8344 :=
@Mathlib.Tactic.Ring.Common.mul_pf_right Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    800)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    20)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    16000)
  Real.pi

noncomputable def p8345 :=
@Mathlib.Meta.NormNum.IsNat.to_raw_eq Real
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      800)
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      20))
  16000

noncomputable def p8346 :=
@Mathlib.Meta.NormNum.isNat_mul Real (@CommSemiring.toSemiring Real Real.instCommSemiring)
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    800)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    20)
  800 20

noncomputable def p8347 :=
@p8346 16000
  (@Eq.refl (Real → Real → Real)
    (@HMul.hMul Real Real Real
      (@instHMul Real
        (@Distrib.toMul Real
          (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (@Mathlib.Meta.NormNum.IsNat.of_raw Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    800)
  (@Mathlib.Meta.NormNum.IsNat.of_raw Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    20)
  (@Eq.refl Nat 16000)

noncomputable def p8348 :=
@p8343
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    p8257
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (p8344
    (@Nat.rawCast Nat
      (@AddCommMonoidWithOne.toAddMonoidWithOne Nat
        (@NonAssocSemiring.toAddCommMonoidWithOne Nat
          (@Semiring.toNonAssocSemiring Nat (@CommSemiring.toSemiring Nat Nat.instCommSemiring))))
      1)
    (@p8345
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      p8347))
  (@Mathlib.Tactic.Ring.Common.mul_zero Real Real.instCommSemiring
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      800))

noncomputable def p8349 :=
p8342
  (p8348
    (@Mathlib.Tactic.Ring.Common.add_pf_add_zero Real Real.instCommSemiring
      (@HAdd.hAdd Real Real Real
        (@instHAdd Real
          (@Distrib.toAdd Real
            (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
        p8257
        (@OfNat.ofNat Real 0
          (@Zero.toOfNat0 Real
            (@MulZeroClass.toZero Real
              (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))))

noncomputable def p8350 :=
@Mathlib.Tactic.Ring.Common.add_pf_add_lt Real Real.instCommSemiring
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    p8257
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    p8257
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (Int.negOfNat 50400))

noncomputable def p8351 :=
p8349
  (p8350
    (@Mathlib.Tactic.Ring.Common.add_pf_zero_add Real Real.instCommSemiring
      (@HAdd.hAdd Real Real Real
        (@instHAdd Real
          (@Distrib.toAdd Real
            (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
        p8257
        (@OfNat.ofNat Real 0
          (@Zero.toOfNat0 Real
            (@MulZeroClass.toZero Real
              (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))))

noncomputable def p8352 :=
@p8337
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 50400))
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      p8257
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))))
  p8351

noncomputable def p8353 :=
p8352
  (@Mathlib.Tactic.Ring.Common.zero_mul Real Real.instCommSemiring
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
        (Int.negOfNat 63))
      (@HAdd.hAdd Real Real Real
        (@instHAdd Real
          (@Distrib.toAdd Real
            (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
        p3819
        (@OfNat.ofNat Real 0
          (@Zero.toOfNat0 Real
            (@MulZeroClass.toZero Real
              (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))))

noncomputable def p8354 :=
p8353
  (@Mathlib.Tactic.Ring.Common.add_pf_add_zero Real Real.instCommSemiring
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
        (Int.negOfNat 50400))
      (@HAdd.hAdd Real Real Real
        (@instHAdd Real
          (@Distrib.toAdd Real
            (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
        p8257
        (@OfNat.ofNat Real 0
          (@Zero.toOfNat0 Real
            (@MulZeroClass.toZero Real
              (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))))

noncomputable def p8355 :=
@Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@Mathlib.Meta.NormNum.instAddMonoidWithOne Real
      (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing)))
    50400)
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    p8255
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (Int.negOfNat 50400))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    p8257
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))

noncomputable def p8356 :=
@Mathlib.Meta.NormNum.isInt_add Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
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
          (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
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
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
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
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (Int.negOfNat 16000))
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    16000)
  (Int.negOfNat 16000) (Int.ofNat 16000)

noncomputable def p8360 :=
@p8359 (Int.ofNat 0)
  (@Eq.refl (Real → Real → Real)
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (@Mathlib.Meta.NormNum.IsInt.of_raw Real
    (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing)) (Int.negOfNat 16000))
  (@Mathlib.Meta.NormNum.IsNat.to_isInt Real
    (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      16000)
    16000
    (@Mathlib.Meta.NormNum.IsNat.of_raw Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      16000))

noncomputable def p8361 :=
@Mathlib.Meta.NormNum.IsInt.to_isNat Real
  (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 16000))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      16000))
  0 (p8360 (@Eq.refl Int (Int.ofNat 0)))

noncomputable def p8362 :=
@Mathlib.Tactic.Ring.Common.add_overlap_pf_zero Real Real.instCommSemiring
  (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (Int.negOfNat 16000))
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    16000)
  Real.pi
  (@Nat.rawCast Nat
    (@AddCommMonoidWithOne.toAddMonoidWithOne Nat
      (@NonAssocSemiring.toAddCommMonoidWithOne Nat
        (@Semiring.toNonAssocSemiring Nat (@CommSemiring.toSemiring Nat Nat.instCommSemiring))))
    1)
  p8361

noncomputable def p8363 :=
@Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero Real Real.instCommSemiring p8255
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  p8257
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  p8362

noncomputable def p8371 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  (@OfNat.ofNat Real 500
    (@instOfNatAtLeastTwo Real 500
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8380 :=
@Mathlib.Tactic.CancelDenoms.sub_subst Real
  (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))
  (@OfNat.ofNat Real 500
    (@instOfNatAtLeastTwo Real 500
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8384 :=
@Mathlib.Tactic.CancelDenoms.div_subst Real Real.instField
  (@OfNat.ofNat Real 1
    (@One.toOfNat1 Real
      (@AddMonoidWithOne.toOne Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))))
  (@OfNat.ofNat Real 500
    (@instOfNatAtLeastTwo Real 500
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8385 :=
@p8384
  (@OfNat.ofNat Real 500
    (@instOfNatAtLeastTwo Real 500
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8387 :=
@HDiv.hDiv Real Real Real
  (@instHDiv Real
    (@DivInvMonoid.toDiv Real
      (@DivisionRing.toDivInvMonoid Real (@Field.toDivisionRing Real Real.instField))))
  (@OfNat.ofNat Real 500
    (@instOfNatAtLeastTwo Real 500
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8388 :=
@Mathlib.Meta.NormNum.isNat_eq_true Real
  (@Mathlib.Meta.NormNum.instAddMonoidWithOne' Real
    (@DivisionSemiring.toSemiring Real
      (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField))))
  (p8387 p4068)
  (@OfNat.ofNat Real 1
    (@One.toOfNat1 Real
      (@AddMonoidWithOne.toOne Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))))
  1

noncomputable def p8389 :=
@Mathlib.Meta.NormNum.isNNRat_div Real
  (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField))
  (@OfNat.ofNat Real 500
    (@instOfNatAtLeastTwo Real 500
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8390 :=
p8250
  (@Inv.inv Real
    (@InvOneClass.toInv Real
      (@DivInvOneMonoid.toInvOneClass Real
        (@DivisionMonoid.toDivInvOneMonoid Real
          (@GroupWithZero.toDivisionMonoid Real
            (@DivisionSemiring.toGroupWithZero Real
              (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField)))))))
    p4068)

noncomputable def p8391 :=
@HMul.hMul Real Real Real
  (@instHMul Real (@Distrib.toMul Real (@instDistribOfSemiring Real Real.semiring)))
  (@OfNat.ofNat Real 500
    (@instOfNatAtLeastTwo Real 500
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8392 :=
p8391
  (@Inv.inv Real
    (@InvOneClass.toInv Real
      (@DivInvOneMonoid.toInvOneClass Real
        (@DivisionMonoid.toDivInvOneMonoid Real
          (@GroupWithZero.toDivisionMonoid Real
            (@DivisionSemiring.toGroupWithZero Real
              (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField)))))))
    p4068)

noncomputable def p8393 :=
@Mathlib.Meta.NormNum.isNNRat_mul Real
  (@DivisionSemiring.toSemiring Real
    (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField)))
  (@HMul.hMul Real Real Real
    (@instHMul Real (@Distrib.toMul Real (@instDistribOfSemiring Real Real.semiring))))
  (@OfNat.ofNat Real 500
    (@instOfNatAtLeastTwo Real 500
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8394 :=
@p8393
  (@Inv.inv Real
    (@InvOneClass.toInv Real
      (@DivInvOneMonoid.toInvOneClass Real
        (@DivisionMonoid.toDivInvOneMonoid Real
          (@GroupWithZero.toDivisionMonoid Real
            (@DivisionSemiring.toGroupWithZero Real
              (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField)))))))
    p4068)

noncomputable def p8395 :=
@Mathlib.Meta.NormNum.IsNat.to_isNNRat Real
  (@DivisionSemiring.toSemiring Real
    (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField)))
  (@OfNat.ofNat Real 500
    (@instOfNatAtLeastTwo Real 500
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8396 :=
@p8394 500 1 1 1 500 1 500
  (@Eq.refl (Real → Real → Real)
    (@HMul.hMul Real Real Real
      (@instHMul Real (@Distrib.toMul Real (@instDistribOfSemiring Real Real.semiring)))))
  (@p8395 500
    (@p8295 500
      (@Eq.refl Real
        (@OfNat.ofNat Real 500
          (@instOfNatAtLeastTwo Real 500
            (@AddMonoidWithOne.toNatCast Real
              (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 498))))))

noncomputable def p8397 :=
@Mathlib.Meta.NormNum.IsNNRat.to_isNat Real
  (@DivisionSemiring.toSemiring Real
    (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField)))
  (p8387 p4068) 1
  (@p8389 p4068 1 1
    (@Mathlib.Meta.NormNum.IsNat.to_isNNRat Real
      (@DivisionSemiring.toSemiring Real
        (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField)))
      p8390 1
      (@Mathlib.Meta.NormNum.IsNNRat.to_isNat Real
        (@DivisionSemiring.toSemiring Real
          (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField)))
        p8392 1
        (p8396 p4091 (@Eq.refl Nat (Nat.mul 500 1))
          (@Eq.refl Nat 500)))))

noncomputable def p8398 :=
@HMul.hMul Real Real Real
  (@instHMul Real
    (@Distrib.toMul Real
      (@instDistribOfSemiring Real
        (@DivisionSemiring.toSemiring Real
          (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField))))))
  (@OfNat.ofNat Real 1
    (@One.toOfNat1 Real
      (@AddMonoidWithOne.toOne Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))))
  (@OfNat.ofNat Real 500
    (@instOfNatAtLeastTwo Real 500
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8399 :=
@Mathlib.Meta.NormNum.isNat_eq_true Real
  (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing))
  p8398
  (@OfNat.ofNat Real 500
    (@instOfNatAtLeastTwo Real 500
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8400 :=
@Mathlib.Meta.NormNum.isNat_mul Real Real.semiring
  (@HMul.hMul Real Real Real
    (@instHMul Real (@Distrib.toMul Real (@instDistribOfSemiring Real Real.semiring))))
  (@OfNat.ofNat Real 1
    (@One.toOfNat1 Real
      (@AddMonoidWithOne.toOne Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))))
  (@OfNat.ofNat Real 500
    (@instOfNatAtLeastTwo Real 500
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8401 :=
@p8400 1 500 500
  (@Eq.refl (Real → Real → Real)
    (@HMul.hMul Real Real Real
      (@instHMul Real (@Distrib.toMul Real (@instDistribOfSemiring Real Real.semiring)))))
  (p3747
    (@Nat.cast_one Real
      (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing))))
  (@p8295 500
    (@Eq.refl Real
      (@OfNat.ofNat Real 500
        (@instOfNatAtLeastTwo Real 500
          (@AddMonoidWithOne.toNatCast Real
            (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing)))
          (Mathlib.Meta.NormNum.instAtLeastTwo 498)))))
  (@Eq.refl Nat 500)

noncomputable def p8403 :=
@Mathlib.Tactic.CancelDenoms.mul_subst Real (@Field.toCommRing Real Real.instField)
  (@OfNat.ofNat Real 1
    (@One.toOfNat1 Real
      (@AddMonoidWithOne.toOne Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))))
  (@OfNat.ofNat Real 500
    (@instOfNatAtLeastTwo Real 500
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8404 :=
@p8403
  (@OfNat.ofNat Real 500
    (@instOfNatAtLeastTwo Real 500
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8405 :=
@p8404
  (@OfNat.ofNat Real 32
    (@instOfNatAtLeastTwo Real 32 Real.instNatCast
      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 31 (instOfNatNat 31))
        (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 30 (instOfNatNat 30))))))
  Real.pi p3705 (p8250 Real.pi)

noncomputable def p8406 :=
@HMul.hMul Real Real Real
  (@instHMul Real
    (@inferInstance (Mul Real)
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real
          (@DivisionSemiring.toSemiring Real
            (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField)))))))
  (@OfNat.ofNat Real 500
    (@instOfNatAtLeastTwo Real 500
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p8407 :=
p8405 (@rfl Real p3930) (@rfl Real (p8406 Real.pi))
  (@p8399 500 p8401
    (@p8295 500
      (@Eq.refl Real
        (@OfNat.ofNat Real 500
          (@instOfNatAtLeastTwo Real 500
            (@AddMonoidWithOne.toNatCast Real
              (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 498))))))

noncomputable def p8411 :=
@Mathlib.Meta.NormNum.isNat_lt_true Real Real.semiring Real.partialOrder Real.instIsOrderedRing
  (@FloorSemiring.instCharZero Real (@Ring.toSemiring Real Real.instRing) Real.partialOrder
    (@FloorRing.toFloorSemiring Real Real.instRing Real.linearOrder Real.instFloorRing))
  (@OfNat.ofNat Real 0 (@Zero.toOfNat0 Real Real.instZero))
  (@OfNat.ofNat Real 500
    (@instOfNatAtLeastTwo Real 500 Real.instNatCast
      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 499 (instOfNatNat 499))
        (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 498 (instOfNatNat 498))))))
  0 500
  (@Mathlib.Meta.NormNum.isNat_ofNat Real
    (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing))
    (@OfNat.ofNat Real 0 (@Zero.toOfNat0 Real Real.instZero)) 0
    (@Nat.cast_zero Real
      (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing))))

noncomputable def p8412 :=
p8411
  (@Mathlib.Meta.NormNum.isNat_ofNat Real
    (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing))
    (@OfNat.ofNat Real 500
      (@instOfNatAtLeastTwo Real 500 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 499 (instOfNatNat 499))
          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 498 (instOfNatNat 498))))))
    500
    (@Eq.refl Real
      (@OfNat.ofNat Real 500
        (@instOfNatAtLeastTwo Real 500
          (@AddMonoidWithOne.toNatCast Real
            (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing)))
          (Mathlib.Meta.NormNum.instAtLeastTwo 498)))))

noncomputable def p8413 :=
@Mathlib.Meta.NormNum.isNat_lt_true Real Real.semiring Real.partialOrder Real.instIsOrderedRing
  (@FloorSemiring.instCharZero Real (@Ring.toSemiring Real Real.instRing) Real.partialOrder
    (@FloorRing.toFloorSemiring Real Real.instRing Real.linearOrder Real.instFloorRing))
  (@OfNat.ofNat Real 0 (@Zero.toOfNat0 Real Real.instZero))
  (@OfNat.ofNat Real 800
    (@instOfNatAtLeastTwo Real 800 Real.instNatCast
      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 799 (instOfNatNat 799))
        (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 798 (instOfNatNat 798))))))
  0 800
  (@Mathlib.Meta.NormNum.isNat_ofNat Real
    (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing))
    (@OfNat.ofNat Real 0 (@Zero.toOfNat0 Real Real.instZero)) 0
    (@Nat.cast_zero Real
      (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing))))

noncomputable def p8414 :=
p8413
  (@Mathlib.Meta.NormNum.isNat_ofNat Real
    (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing))
    (@OfNat.ofNat Real 800
      (@instOfNatAtLeastTwo Real 800 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 799 (instOfNatNat 799))
          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 798 (instOfNatNat 798))))))
    800
    (@Eq.refl Real
      (@OfNat.ofNat Real 800
        (@instOfNatAtLeastTwo Real 800
          (@AddMonoidWithOne.toNatCast Real
            (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing)))
          (Mathlib.Meta.NormNum.instAtLeastTwo 798)))))

noncomputable def p9466 :=
nat_lit
  65315689001430101463437438788805272313419085489526239767007691747054552085219169171183189876641515636152014546297038989853108186772682866843307077206540288000

noncomputable def p9469 :=
nat_lit
  9993300417218805523905928134687206663953120079897514684352176837299346469038532883191028051126151892331258225583446965447525552576220478627025982812600664064000

noncomputable def p10041 :=
nat_lit 253530120045645880299340641075200000000000000

noncomputable def p12328 :=
nat_lit
  115402833396154575366545869793535889621349127769526229668542875625964151543596233127717554347659978665736274395563047822181610776723872051477952309687675478936779750458329093309163388859169570944610465113807304808518412809535488000

noncomputable def p12330 :=
nat_lit
  17656633509611650031081518078410991112066416548737513139287059970772515186170223668540785815191976735857649982521146316793786448838752423876126703382214348277327301820124351276301998495452944354525401162412517635703317159858929664000

noncomputable def p12450 :=
nat_lit 1393796574908163946345982392040522594123776

noncomputable def p13788 :=
nat_lit
  418993997810706159361688281193932691483730181893512293053861295116305125939798343025058571817715732115313495568327689089179808837873330310826051531440128

noncomputable def p14600 :=
nat_lit 215679573337205118357336120696157045389097155380324579848828881993728

noncomputable def p15946 :=
nat_lit 242833611528216133864932738352939863330300854881517440156476551217363035650651062272

noncomputable def p16541 :=
nat_lit 30354201441027016733116592294117482916287606860189680019559568902170379456331382784

noncomputable def p16711 :=
nat_lit 13479973333575319897333507543509815336818572211270286240551805124608

noncomputable def p17975 :=
nat_lit
  818347651974035467503297424206899788054160511510766197370822842024033449101168638720817523081476039287721671031890017752304314136471348263332131897344

noncomputable def p18792 :=
nat_lit 883423532389192164791648750371459257913741948437809479060803100646309888

noncomputable def p18799 :=
nat_lit 441711766194596082395824375185729628956870974218904739530401550323154944

noncomputable def p20387 :=
nat_lit
  2521728396569246669585858566409191283525103313309788586748690777871726193375821479130513040312634601011624191379636224

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
Enclosure.Real.IsNear (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) Real.pi Real.pi) false
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
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) Real.pi Real.pi))
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
@Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) Real.pi Real.pi)
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
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) Real.pi Real.pi)))
  false 19012918537349

noncomputable def p20567 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 96 1)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) Real.pi Real.pi)))
  false 19012918537349

noncomputable def p20568 :=
nat_lit 66316183694144421773210654158497289952536449997343430808550413743407747667300117573677859187588642844427

noncomputable def p20569 :=
nat_lit 1252767871951132907648062937299067324180438397275293511571549967224543529962146817001239

noncomputable def p20570 :=
@Enclosure.Real.IsNear.inv_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 96 1)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) Real.pi Real.pi))
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

noncomputable def p20575 :=
nat_lit
  359538626972463181545861038157804946723595395788461314546860162315465351611001926265416954644815072042240227759742786715317579537628833244985694861278948248755535786849730970552604439202492188238906165904170011537676301364684925762947826221081654474326701021369172596479894491876959432609670712659248448274432

noncomputable def p20578 :=
nat_lit
  179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416622492847430639474124377767893424865485276302219601246094119453082952085005768838150682342462881473913110540827237163350510684586298239947245938479716304835356329624224137216

noncomputable def p20588 :=
nat_lit
  1438154507889852726183444152631219786894381583153845258187440649261861406444007705061667818579260288168960911038971146861270318150515332979942779445115792995022143147398923882210417756809968752955624663616680046150705205458739703051791304884326617897306804085476690385919577967507837730438682850636993793097728

noncomputable def p20639 :=
nat_lit 35651584000000000000000000

noncomputable def p20660 :=
nat_lit 27200000000000000000000000

noncomputable def p20778 :=
nat_lit
  5765353595857776242624860871642479886919875261061710514480556676432029053838785212846868915030614583352860005060453947473989179403103839466467660368207274948480973235352179792670708534870016000

noncomputable def p20781 :=
nat_lit
  328625154963893245829617069683621353554432889880517499325391730556625656068810757132271528156745031251113020288445875006017383225976918849588656640987814672063415474415074248182230386487590912000

noncomputable def p20890 :=
nat_lit
  98829225247710262867429368515096341332791332892647518728955741224331220492185227974590031104217345944915565363435943316108305047551656971126471386689813725547615929822542168634993607295943953291620980311754270053008792716515963231747120779125566189619536160406425180445475300105093018814544105228831057745755716670455808

noncomputable def p20899 :=
nat_lit
  404804506614621236704990693437834614099113299528284236713802716054860679135990693783920767402874248990374155728633623822779617474771586953734026799881477019843034848553132722728933815484186432682479535356945490137124014966849385397236206711298319112681620113024717539104666829230461005064372655017292012526615415482186989568

noncomputable def p20904 :=
nat_lit
  44942328371557897693232629769725618340449424473557664318357520289433168951375240783177119330601884005280028469967848339414697442203604155623211857659868531094441973356216371319075554900311523529863270738021251442209537670585615720368478277635206809290837627671146574559986811484619929076208839082406056034304

noncomputable def p20924 :=
nat_lit
  89884656743115795386465259539451236680898848947115328636715040578866337902750481566354238661203768010560056939935696678829394884407208311246423715319737062188883946712432742638151109800623047059726541476042502884419075341171231440736956555270413618581675255342293149119973622969239858152417678164812112068608

noncomputable def p20927 :=
nat_lit 32112092083513587453132800000000

noncomputable def p20932 :=
nat_lit 1197262141301475670592458614961179049702139939205939200000000000000000000000000000000000000000000000000

noncomputable def p20947 :=
nat_lit
  53102990615883956733387301248634318761034095274990519830731939129350906266306940335926087483461735510804137932871510655900434920930053303934669231053358814434699611628336331660878506027009877679359193392996227855949211921999426701532324897040027625005419272233679190997940926390958862794299232502772129059116465853813021764814338443329201266457768197681217975241444878096295327802569303860828984006294896640000

noncomputable def p20950 :=
nat_lit
  12266790832269194005412466588434527633798876008522810080899077938880059347516903217598926208679660902995755862493318961513000466734842313208908592373325886134415610286145692613662934892239281743931973673782128634724267953981867568053967051216246381376251851885979893120524353996311497305483122708140361812655903612230808027672112180409045492551744453664361352280773766840244220722393509191851495305454121123840000

noncomputable def p21002 :=
nat_lit
  306180206916083902309240650087602475282639486413866622577088471913520022894784390350900738050555138105234536857820245071373614031482942161565170086143298589738273508330367307539078392896587187265470464

noncomputable def p21004 :=
nat_lit
  214524926879081553593184399971293538039669853129478294043576983099548224481176751628829988770670454843040509730983776813660062124991145119142938384097345536000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p21008 :=
nat_lit
  45427420268475430659332737993000283397102585042957378767593137448789955507087370207886940669610222847547657600391636120845912601788416

noncomputable def p21010 :=
nat_lit
  358359158748448673689190764890951084499463279557543925583998256154206699388825751260940398923457138524160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p21012 :=
nat_lit 6739986666787659948666753771754907668409286105635143120275902562304

noncomputable def p21014 :=
nat_lit 598631070650737835296229307480589524851069969602969600000000000000000000000000000000000000000000000000

noncomputable def p21028 :=
nat_lit 64224184167027174906265600000000

noncomputable def p21033 :=
nat_lit
  21567957333720511835733612069615704538909715538032457984882888199372800000000000000000000000000000000000000000000000000

noncomputable def p21036 :=
nat_lit 324518553658426726783156020576256

noncomputable def p21065 :=
nat_lit
  19892929456391465686215289925872833604018246031893908697618559075726379880501335021322240000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p21092 :=
nat_lit 1684996666696914987166688442938726917102321526408785780068975640576

noncomputable def p21094 :=
nat_lit 3975284453540055937514022744988289813464136516894720000000000000000000000000000000000000000000000000000000000

noncomputable def p21110 :=
nat_lit
  1115162802933563091401133326221320693981716000774800916445370721716369031592445747054447837152696445726886896590301723773909133339531119382628053852120535103128691844195062964878448626567207431266543061252920784974933450361987960732178822837840580125113804716907263010956759454210136118680283882558214710241445782930073457061101107309913226595613132151305577480070342440022201883853955381077408664132192829440000

noncomputable def p21112 :=
nat_lit
  94045396380730487374828910511331378525791382732008210620226264198080454997629591334925100933210733589634128279115445371599670244967124401268299208195498460363853012193783643371415834173834493370145131498996319532886054313860984688413747392657888923884597531125845847257353380638388146008703940762409440563695261027102861545486193383136015442896707478093437034152598879108539025538350237137528130675148261949440000

noncomputable def p21153 :=
nat_lit 3369993333393829974333376885877453834204643052817571560137951281152

noncomputable def p21166 :=
nat_lit 1987642226770027968757011372494144906732068258447360000000000000000000000000000000000000000000000000000000000

noncomputable def p21205 :=
nat_lit
  10086913586276986678343434265636765134100413253239154346994763111486904773503285916522052161250538404046496765518544896

noncomputable def p21208 :=
nat_lit
  264202969342699153645046819327998571303367330111090974890246487724490982787908355751936000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p21235 :=
nat_lit
  17559299170990978409660250369620480745441999391238719887248483624476403829714520123481588402304937253764141569414682954956800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p22163 :=
nat_lit
  258635847866053699551804458606442576272367825490694860258120615482457469359601887045902088741239297471068878038951060359940017752541043355611647990255336180740663842822668939079742833331455582650152405220392778446708973621073329905620841187774760612760151038282022499508170002936410485183057600467309433716715

noncomputable def p22164 :=
Enclosure.Real.IsNear
  (hardyZApproximantRS
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
      true 5))
  false p22163 p20575

noncomputable def p22165 :=
nat_lit
  623553005727327308365835859946061654117700557883230884327264417774347586552411812995645893847272616785772126694731285426129157954060711651992721126438985521630898795129819043372905314983054078862141745963737293050286793561117382235462991501272074216933575507563679731650633596686078332464286828172857055

noncomputable def p22166 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZApproximantRS
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
      true 5))
  (hardyZApproximantRS
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
      true 5))
  false p22163

noncomputable def p22167 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
  (Zeta.RiemannSiegel.mainSumOfPhase
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
        true 5))
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
      true 5)
    12)

noncomputable def p22168 :=
@HPow.hPow Real Real Real (@instHPow Real Real Real.instPow)
  (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
      true 5)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@OfNat.ofNat Real 2
        (@instOfNatAtLeastTwo Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p22169 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  (@HPow.hPow Real Nat Real
    (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))
    (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)))
    12)
  (p22168
    (@Neg.neg Real Real.instNeg
      (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
        (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))
        (@OfNat.ofNat Real 4
          (@instOfNatAtLeastTwo Real 4 Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 3 (instOfNatNat 3))
              (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 2 (instOfNatNat 2)))))))))

noncomputable def p22170 :=
Real.sqrt
  (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
      true 5)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@OfNat.ofNat Real 2
        (@instOfNatAtLeastTwo Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p22171 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p22169
  (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
        (Enclosure.sfrac false 12 1)))
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Zeta.RiemannSiegel.correctionLinear
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
          (Enclosure.sfrac false 12 1)))
      (@Inv.inv Real Real.instInv p22170)))

noncomputable def p22172 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZApproximantRS
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
      true 5))
  (p22167 p22171) false p22163

noncomputable def p22173 :=
@BSN.floor_sqrt_eq_dec
  (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
    true 5)
  102026600 100000 12
  (Enclosure.sfrac_ofScientific_eq 102026600 5 100000 (Eq.refl true))

noncomputable def p22174 :=
nat_lit
  2494212022909309233463343439784246616470802231532923537309057671097390346209647251982583575389090467143088506778925141704516631816242846607970884505755942086523595180519276173491621259932216315448566983854949172201147174244469528941851966005088296867734302030254718926602534386744313329857147312691428219

noncomputable def p22175 :=
nat_lit
  719077253944926363091722076315609893447190791576922629093720324630930703222003852530833909289630144084480455519485573430635159075257666489971389722557896497511071573699461941105208878404984376477812331808340023075352602729369851525895652442163308948653402042738345192959788983753918865219341425318496896548864

noncomputable def p22176 :=
@Enclosure.Real.IsNear.recentre' (p22167 p22171) false p22163
  p20575 p22174 p22175 p22163
  p20575 p22165 p20578

noncomputable def p22177 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (Zeta.RiemannSiegel.mainSumOfPhase
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
        true 5))
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
      true 5)
    12)

noncomputable def p22178 :=
nat_lit
  49570847282784739224624144608333278973343895494782362243409034907490767436901891534140516868697639302159437821521293197464707830145022013664627093132196514514225590142836839168509048016611616210980295673596653987373273738186185577325062761562690384049940332158602908579975581976701262034694886040674078294037

noncomputable def p22179 :=
nat_lit
  202993867095572403416175529458805440240754557846607567712320207340191350042954007944710561515836441916599128204255320529873537156174036452419623705473985021295153028489160851947915440842106967461240341680361754914203763496682970015037937685689007876559250375622220554866762221482444586092464632322800507

noncomputable def p22180 :=
nat_lit
  17773320130526912450476960120026505599868886383442713233982690590728737481766594695072568351387401426372101397451318694247429836301171233761122019116972729372267140196048758732520188883983687288944473437397226491251019528515786373799364471640038269536540304023067690561980259958721712023883599476661253358809130456842240

noncomputable def p22181 :=
@p22177 p22171 58908281971 68719476736 218963
  68719476736 p22178 p20575 p22179
  p22175 p22180 p22163

noncomputable def p22182 :=
@Enclosure.Real.IsNear.of_eq
  (Zeta.RiemannSiegel.mainSumOfPhase
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
        true 5))
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
      true 5)
    12)

noncomputable def p22183 :=
@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
        true 5))
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
      true 5)
    12)

noncomputable def p22184 :=
p22183
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
        true 5))
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
      true 5)
    12)

noncomputable def p22185 :=
@p22182 p22184 false 58908281971 68719476736
  218963 68719476736
  (BSN.main_sum_of_phase_eq
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
        true 5))
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
      true 5)
    12)

noncomputable def p22186 :=
@Enclosure.Real.IsNear.addLit_ff
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
        true 5))
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
      true 5)
    12)

noncomputable def p22187 :=
@p22186
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
        true 5))
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
      true 5)
    12)

noncomputable def p22188 :=
@p22187 58908281971 137438953472 218963 137438953472
  58908281971 137438953472 218963 137438953472 16192585249855450906624
  58908281971 68719476736

noncomputable def p22189 :=
BSN.mainSumRS_step
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
      true 5))
  (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
    true 5)
  Real.sin BSN.quadSignNeg

noncomputable def p22190 :=
p22189 11 12 102026600 100000 285
  137438953472 68719476736 2305843009213693952 false 286700611133511
  3341

noncomputable def p22191 :=
p22190 341522969406 43 39675208392 8 false
  98583250647 205324 true 215410837850 7244019458077122842 1

noncomputable def p22192 :=
p22191 false 137438123068 true false 58908281971 218963
  BSN.abs_quadSignNeg (BSN.cos_quad_nat1 285 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 137438123068 137438953472)
  (Enclosure.sfrac_ofScientific_eq 102026600 5 100000 (Eq.refl true))
  (Eq.refl true)

noncomputable def p22193 :=
BSN.mainSumRS_step2
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
      true 5))
  (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
    true 5)
  Real.sin Real.sin

noncomputable def p22194 :=
p22193 BSN.quadSignPos BSN.quadSignNeg 9 10 11 102026600
  100000 167 229 137438953472 68719476736

noncomputable def p22195 :=
p22194 2305843009213693952 false 286700611133511 3341
  316464885454 43 43462013224 8 329564216814 43
  41439403656

noncomputable def p22196 :=
p22195 8 false 92872186792 176140 true 124354942616
  true 104063949072 7244019458077122842 1 false

noncomputable def p22197 :=
p22196 108068578983 false false 94401825900 true false
  98583250647 205324 BSN.abs_quadSignPos
  (BSN.cos_quad_nat3 167 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 108068578983 137438953472)

noncomputable def p22198 :=
BSN.mainSumRS_step2
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
      true 5))
  (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
    true 5)
  Real.cos Real.sin

noncomputable def p22199 :=
p22198 BSN.quadSignNeg BSN.quadSignPos 7 8 9 102026600
  100000 22 99 137438953472 68719476736

noncomputable def p22200 :=
p22199 2305843009213693952 false 286700611133511 3341
  285796269294 43 48592008000 16 301984246446 43
  45812984488

noncomputable def p22201 :=
p22200 8 false 108801946364 143683 true 138056082009
  true 30676327000 7244019458077122842 1 false

noncomputable def p22202 :=
p22201 73738540868 true false 30422254713 false false
  92872186792 176140 BSN.abs_quadSignNeg
  (BSN.cos_quad_nat2 22 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 73738540868 137438953472)

noncomputable def p22203 :=
BSN.mainSumRS_step2
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
      true 5))
  (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
    true 5)
  Real.cos Real.cos

noncomputable def p22204 :=
p22203 BSN.quadSignPos BSN.quadSignPos 5 6 7 102026600
  100000 164 64 137438953472 68719476736

noncomputable def p22205 :=
p22204 2305843009213693952 false 286700611133511 3341
  246257546308 43 56109217800 8 267443854420 43
  51947041624

noncomputable def p22206 :=
p22205 8 false 4492648537 106544 false 46678455367
  false 19868950404 7244019458077122842 1 false

noncomputable def p22207 :=
p22206 129588143177 false false 136005269215 false false
  108801946364 143683 BSN.abs_quadSignPos
  (BSN.cos_quad_nat0 164 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 129588143177 137438953472)

noncomputable def p22208 :=
BSN.mainSumRS_step2
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
      true 5))
  (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
    true 5)
  Real.sin Real.cos

noncomputable def p22209 :=
p22208 BSN.quadSignPos BSN.quadSignNeg 3 4 5 102026600
  100000 427 282 137438953472 68719476736

noncomputable def p22210 :=
p22209 2305843009213693952 false 286700611133511 3341
  190530846192 42 68719476728 8 221199462352 42
  61464568544

noncomputable def p22211 :=
p22210 16 true 16343897775 62762 false 124033215289
  false 137734354682 7244019458077122842 1 false

noncomputable def p22212 :=
p22211 107869506470 false false 74009840598 true false
  4492648537 106544 BSN.abs_quadSignPos
  (BSN.cos_quad_nat3 427 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 107869506470 137438953472)

noncomputable def p22213 :=
p22208 BSN.quadSignNeg BSN.quadSignNeg 1 2 3 102026600
  100000 877 614 137438953472 68719476736

noncomputable def p22214 :=
p22213 2305843009213693952 false 286700611133511 3341
  95265423088 42 97184016000 16 150992123216 42
  79350416784

noncomputable def p22215 :=
p22214 16 false 137437868976 3393 false 170233911356
  false 92879139191 7244019458077122842 1 false

noncomputable def p22216 :=
p22215 129925600119 true false 107232120881 true true
  16343897775 62762 BSN.abs_quadSignNeg
  (BSN.cos_quad_nat1 877 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 129925600119 137438953472)

noncomputable def p22217 :=
@Enclosure.Real.IsNear.recentre'
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
        true 5))
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
      true 5)
    1)

noncomputable def p22218 :=
@Enclosure.Real.IsNear.of_eq
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
        true 5))
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
      true 5)
    1)

noncomputable def p22219 :=
@p22218
  (Real.cos
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
        true 5)))
  false 8589866811

noncomputable def p22220 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
        true 5)))
  false 17179733622

noncomputable def p22221 :=
@Enclosure.Real.IsNear.cos_image
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
      true 5))
  (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
    (@Nat.cast Real Real.instNatCast 4479697048961)
    (@Nat.cast Real Real.instNatCast 2147483648))
  false 4479697048961

noncomputable def p22222 :=
nat_lit 119209776603754532960019299275058903151206586867798125071

noncomputable def p22223 :=
nat_lit 57146955059754571597839708823201140353860537449185280

noncomputable def p22224 :=
@Enclosure.Real.IsNear.recentre'
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
      true 5))
  false p22222 p22223

noncomputable def p22225 :=
nat_lit 17825792000000000000000000

noncomputable def p22226 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 102026600 400000)
      (Real.log (Enclosure.sfrac false 41637718430240000 160000000000)))
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 1 4)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 1 2) Real.pi)
        (Real.arctan
          (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
            (@Nat.cast Real Real.instNatCast 100000)
            (@Nat.cast Real Real.instNatCast 204053200))))))

noncomputable def p22227 :=
nat_lit 530650493597419072266031936916480000000000000000

noncomputable def p22228 :=
nat_lit 3248428303081401031581646567656272302080000000000000

noncomputable def p22229 :=
@Enclosure.Real.IsNear.of_eq
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
      true 5))
  (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (p22226 (Enclosure.sfrac false 102026600 200000))
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 102026600 200000) (Real.log Real.pi)))
    (Enclosure.sfrac true p22227 p22228))
  false

noncomputable def p22230 :=
BSN.riemannSiegelThetaApproximant_two_zero_mk
  (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
    true 5)
  102026600 100000 41637718430240000 160000000000

noncomputable def p22231 :=
p22230 204053200 400000 200000 p22227
  p22228
  (Enclosure.sfrac_ofScientific_eq 102026600 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p22232 :=
@Enclosure.Real.IsNear.addLit_ft_p
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (p22226 (Enclosure.sfrac false 102026600 200000))
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 102026600 200000) (Real.log Real.pi)))
  (Enclosure.sfrac true p22227 p22228) 751568508905059740651
  360287970189639680

noncomputable def p22233 :=
nat_lit 2441416224844892835021195249153206336536710899052505601454080000000000000

noncomputable def p22234 :=
@p22232 433204801216492481 p22225 p22227
  p22228 0 1 p22233 p22222
  p22223 433204801216492481 p22225

noncomputable def p22235 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (p22226 (Enclosure.sfrac false 102026600 200000))
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 102026600 200000) (Real.log Real.pi))
  24049097249435738409459 9007199254740992000 321480557687 34000000000000000000

noncomputable def p22236 :=
nat_lit 1291184866580286542008914699878400000

noncomputable def p22237 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 102026600 400000)
      (Real.log (Enclosure.sfrac false 41637718430240000 160000000000)))
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 1 4)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 1 2) Real.pi)
        (Real.arctan
          (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
            (@Nat.cast Real Real.instNatCast 100000)
            (@Nat.cast Real Real.instNatCast 204053200))))))

noncomputable def p22238 :=
@p22237 (Enclosure.sfrac false 102026600 200000)
  5728793365370904976279 1801439850948198400 321480557687 34000000000000000000
  102026600 200000 0

noncomputable def p22239 :=
nat_lit 961963889977429536378360000

noncomputable def p22240 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 102026600 400000)
    (Real.log (Enclosure.sfrac false 41637718430240000 160000000000)))
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 1 4)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 1 2) Real.pi)
      (Real.arctan
        (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
          (@Nat.cast Real Real.instNatCast 100000)
          (@Nat.cast Real Real.instNatCast 204053200)))))
  5729500568439000185079

noncomputable def p22241 :=
nat_lit 12900095832783488697259503529012232192

noncomputable def p22242 :=
@p22240 1801439850948198400 318980553437 34000000000000000000
  884003835119011 2251799813685248 10000017 136000000000000000
  p22241 5728793365370904976279 1801439850948198400 321480557687

noncomputable def p22243 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 102026600 400000)
  (Real.log (Enclosure.sfrac false 41637718430240000 160000000000)) 102026600
  400000 0 1 56156929354099815 4503599627370496

noncomputable def p22244 :=
nat_lit 30872598402514061944915230720

noncomputable def p22245 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
      (@Nat.cast Real Real.instNatCast 41637718430240000)
      (@Nat.cast Real Real.instNatCast 160000000000)))
  false p22244 p2333

noncomputable def p22246 :=
BSN.log_rat_reduce_isNear 41637718430240000 160000000000 17 83275436860480000
  41943040000000000 47130643077 68719476736 24973259072661432
  36028797018963968 27200000000 1000000000000000

noncomputable def p22247 :=
nat_lit
  1061827631922700529510804540245396832320109177022661583842225222534785329457453001909674990883241469781908127788647741842972656766347190864899133692081499043689985689552959718830833982174188752003126666803391009398607474767128638797738409313687225386541639507538485004620922223616602172030976000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p22248 :=
nat_lit
  41299013528522201107498722238643260922263324493361253878996765542078749922993161209022818933695962982775281361510858150756754486896474631088545706970159831344828555344596940385265964018355852840313525540943092307889493264515864187830277739818011112327393816937869793844551025630057768524185600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p22249 :=
nat_lit
  1185807008290357744104912165120059976088187076836154920988720557823594801310168134000263992046915968538235103758473168940308198514329710638360305394681762825457988072760343223385149985940939317221329877266547054676982484534396377788992874024450904140691889721076748117869080870912000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p22250 :=
BSN.log_dyadic_bound 20666198430240000 62609238430240000 12 11
  p22247 68719476736 27200000000 p22248 p22249
  47130643077 83275436860480000

noncomputable def p22251 :=
p22250 41943040000000000 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p22252 :=
@BSN.binarySplit_of_base11 (BSN.artanhP 20666198430240000) (BSN.artanhQ 62609238430240000)
  0 11 p22248 p22247 p22249
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p22253 :=
p22246 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p22251 (p22252 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

noncomputable def p22254 :=
@p22243 625289 17000000000000000 5729500568439000185079
  1801439850948198400 318980553437 34000000000000000000
  (Enclosure.Real.IsNear.const false 102026600 400000)
  (BSN.isNear_log_sfrac 41637718430240000 160000000000 56156929354099815
    4503599627370496 625289 17000000000000000 false
    (@p22245 1000462400000000 p20660 56156929354099815
      4503599627370496 625289 17000000000000000
      (p22253 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p22255 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 1 4)
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 1 2) Real.pi)
    (Real.arctan
      (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
        (@Nat.cast Real Real.instNatCast 100000)
        (@Nat.cast Real Real.instNatCast 204053200))))
  1 4

noncomputable def p22256 :=
@p22255 0 1 884003835119011 562949953421312 10000017
  34000000000000000 884003835119011 2251799813685248 10000017
  136000000000000000 (Enclosure.Real.IsNear.const false 1 4)

noncomputable def p22257 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 1 2) Real.pi)
  (Real.arctan
    (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
      (@Nat.cast Real Real.instNatCast 100000) (@Nat.cast Real Real.instNatCast 204053200)))
  884279719003555 562949953421312 1

noncomputable def p22258 :=
nat_lit 7593535122749457025728512

noncomputable def p22259 :=
@p22257 2000000000000000 4209654 8589934592 1
  3400000000 p22258 884003835119011 562949953421312 10000017
  34000000000000000
  (@p803 1 1000000000000000 884279719003555 562949953421312
    1 2000000000000000 (Enclosure.Real.IsNear.const false 1 2)
    BSN.pi_near_15 (Eq.refl true))

noncomputable def p22260 :=
BSN.arctan_dyadic_bound_f 100000 204053200 1 0 8589934592
  3400000000 0 1 1 0 1

noncomputable def p22261 :=
p22260 1 4209654 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)
  (@BSN.binarySplit_of_le (BSN.arctanEvenP 100000) (BSN.arctanEvenQ 204053200) 0
    0 (Eq.refl true))
  (@BSN.binarySplit_of_le (BSN.arctanOddP 100000) (BSN.arctanOddQ 204053200) 0 0
    (Eq.refl true))

noncomputable def p22262 :=
p22256
  (p22259
    (p22261 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p22263 :=
@p22235 40129734243844947 68719476736000 510133 34359738368000
  p22236 751568508905059740651 360287970189639680 433204801216492481
  p22225
  (@p22238 1 p22239 24049097249435738409459
    9007199254740992000 321480557687 34000000000000000000
    (@p22242 34000000000000000000 p22254 p22262
      (Eq.refl true) (Eq.refl true))
    (Enclosure.Real.IsNear.const false 102026600 200000) (Eq.refl true)
    (Eq.refl true))

noncomputable def p22264 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 102026600 200000) (Real.log Real.pi)
  102026600 200000 0 1 78665238759 68719476736

noncomputable def p22265 :=
p22263
  (@p22264 1 34359738368 40129734243844947 68719476736000
    510133 34359738368000
    (Enclosure.Real.IsNear.const false 102026600 200000) d258
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p22266 :=
@p22221 2147483648 419 17179869184 false 17179733622
  17179869184 1 3400000000
  (@p22224 433204801216492481 p22225 4479697048961
    2147483648 419 17179869184
    (@p22229 p22222 p22223 433204801216492481
      p22225
      (p22231 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p22234 (p22265 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p22227 p22228)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p22267 :=
nat_lit 1229455271693462349545472

noncomputable def p22268 :=
BSN.cos_reduce0
  (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
    (@Nat.cast Real Real.instNatCast 4479697048961)
    (@Nat.cast Real Real.instNatCast 2147483648))
  (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
    (@Nat.cast Real Real.instNatCast p22267)
    (@Nat.cast Real Real.instNatCast p976))
  226375608064910080 72057594037927936 false

noncomputable def p22269 :=
BSN.sin_reduce_arg_pos_rat_q0 4479697048961 2147483648 226375608064910080
  72057594037927936 332 p22267 p976
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p22270 :=
BSN.cos_dyadic_bound_f 139772881959 35184372088832 1 0 17179869184
  6806640626 0 1 1 0 1

noncomputable def p22271 :=
p22270 1 17179733622 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (@BSN.binarySplit_of_le (BSN.cosEvenP 139772881959) (BSN.cosEvenQ 35184372088832) 0
    0 (Eq.refl true))

noncomputable def p22272 :=
p22271
  (@BSN.binarySplit_of_le (BSN.cosOddP 139772881959) (BSN.cosOddQ 35184372088832) 0
    0 (Eq.refl true))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p22273 :=
@BSN.cos_arg_round false 17179733622 17179869184 p22267
  p976 139772881959 35184372088832 6806640626 6800000000
  p22272 (Eq.refl true)

noncomputable def p22274 :=
p22268 17179733622 17179869184 332 1000000000000000
  6800000000 3400000000 p22269 BSN.pi_near_15 p22273
  (Eq.refl true) (Eq.refl true)

noncomputable def p22275 :=
@p22219 8589934592 2815976307 114085068800000000
  (BSN.main_sum_rs_one
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
        true 5))
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
      true 5))
  (@p22220 17179869184 1441779869184 58411555225600000000
    8589866811 8589934592 2815976307 114085068800000000
    (p22266 (Enclosure.sfrac_false_div 4479697048961 2147483648)
      (p22274 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p22276 :=
@p22217 false 8589866811 8589934592 2815976307
  114085068800000000 137437868976 137438953472 3393 137438953472
  p22275 (Eq.refl true)

noncomputable def p22277 :=
p22216 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 614 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 107232120881 137438953472)
  (Enclosure.sfrac_ofScientific_eq 102026600 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true) p22276
  (@p22224 433204801216492481 p22225 286700611133511
    137438953472 3341 137438953472
    (@p22229 p22222 p22223 433204801216492481
      p22225
      (p22231 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p22234 (p22265 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p22227 p22228)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p22278 :=
nat_lit
  5552646641146775532856772882762430119516555228604874148044549227958492452015918273967670792612940225530335292998183400997932765021416965799936

noncomputable def p22279 :=
nat_lit
  592315275786481478594449143491399829760996115325527777129953850166072819291994284378170629727717480692141726402833631312619606728769536

noncomputable def p22280 :=
nat_lit
  27749882980992705701380477985974092243485096836264558378550223722584638778948039522324482113826433737683226470549672902719330168412375084957696

noncomputable def p22281 :=
BSN.sin_dyadic_bound_f 170233911356 137438953472 4 3 137438953472
  68719476736 p22278 p2504 p22279
  p22280 p2507

noncomputable def p22282 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 170233911356) (BSN.sinEvenQ 137438953472) 0
  3 p22278 p2504 p22279 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p22283 :=
p22281 p22279 129925600119 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p22282 (Eq.refl true))

noncomputable def p22284 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 170233911356) (BSN.sinOddQ 137438953472) 0
  3 p22280 p2507 p22279 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p22285 :=
nat_lit
  189117221272571619670644895086772121190580028384140590709884608161627591866787845548147468807923643944330789098921869816922477381995086952161

noncomputable def p22286 :=
nat_lit
  412114770467495821721172516861822255030043047120565143504071317421835260590841553593103999292820805850795698155410435671537600902881

noncomputable def p22287 :=
nat_lit
  1147216197916207522562428213017200039806352249866335009563325830003285433230909650683974091634654193342847752751656892010252609671362034480865

noncomputable def p22288 :=
BSN.cos_dyadic_bound_f 92879139191 137438953472 4 3 137438953472
  68719476736 p22285 p2457 p22286
  p22287 p2460

noncomputable def p22289 :=
@BSN.binarySplit_of_base3 (BSN.cosEvenP 92879139191) (BSN.cosEvenQ 137438953472) 0
  3 p22285 p2457 p22286 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p22290 :=
p22288 p22286 107232120881 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p22289 (Eq.refl true))

noncomputable def p22291 :=
@BSN.binarySplit_of_base3 (BSN.cosOddP 92879139191) (BSN.cosOddQ 137438953472) 0
  3 p22287 p2460 p22286 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p22292 :=
p22277 d93 d95 d97 d99 d103
  (p22283 (p22284 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p22290 (p22291 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p22293 :=
p22212 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 282 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 74009840598 137438953472)
  (Enclosure.sfrac_ofScientific_eq 102026600 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p22292 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p22224 433204801216492481 p22225 286700611133511
    137438953472 3341 137438953472
    (@p22229 p22222 p22223 433204801216492481
      p22225
      (p22231 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p22234 (p22265 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p22227 p22228)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p22294 :=
nat_lit
  1563957867137112087859762317944048484285842217006008534196052538327425414048209500988366415862005765780590659169388453711977994826711812818721

noncomputable def p22295 :=
nat_lit
  13257328684335258106068211879960990124367687933520559625947406550923144798504948480445107133507132527383798475839105764144232935737121

noncomputable def p22296 :=
nat_lit
  7818729182522054958747453749428624209870476693849843209920133625261658392725897146253111538141566221821356191044293394448086295148874376955681

noncomputable def p22297 :=
BSN.sin_dyadic_bound_f 124033215289 137438953472 4 3 137438953472
  68719476736 p22294 p2504 p22295
  p22296 p2507

noncomputable def p22298 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 124033215289) (BSN.sinEvenQ 137438953472) 0
  3 p22294 p2504 p22295 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p22299 :=
p22297 p22295 107869506470 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p22298 (Eq.refl true))

noncomputable def p22300 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 124033215289) (BSN.sinOddQ 137438953472) 0
  3 p22296 p2507 p22295 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p22301 :=
nat_lit
  915027687465974054279465005722461602884846667008325032628434791262000965495875575268137661606727204555200777933499829283104763115905006637056

noncomputable def p22302 :=
nat_lit
  46613030924783093734412359852537573702209361546874246618534685382006962499525131879667872159941853044724477439017782469284734556901376

noncomputable def p22303 :=
nat_lit
  5548947223592861889545010855762063644648290980322596266656282967764095616709528977180376546779587265330770548866786763852076308970283592519680

noncomputable def p22304 :=
BSN.cos_dyadic_bound_f 137734354682 137438953472 4 3 137438953472
  68719476736 p22301 p2457 p22302
  p22303 p2460

noncomputable def p22305 :=
@BSN.binarySplit_of_base3 (BSN.cosEvenP 137734354682) (BSN.cosEvenQ 137438953472) 0
  3 p22301 p2457 p22302 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p22306 :=
p22304 p22302 74009840598 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p22305 (Eq.refl true))

noncomputable def p22307 :=
@BSN.binarySplit_of_base3 (BSN.cosOddP 137734354682) (BSN.cosOddQ 137438953472) 0
  3 p22303 p2460 p22302 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p22308 :=
p22293 d105 d107 d109 d111 d103
  (p22299 (p22300 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p22306 (p22307 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p22309 :=
p22207 BSN.abs_quadSignPos (BSN.cos_quad_nat0 64 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 136005269215 137438953472)
  (Enclosure.sfrac_ofScientific_eq 102026600 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p22308 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p22224 433204801216492481 p22225 286700611133511
    137438953472 3341 137438953472
    (@p22229 p22222 p22223 433204801216492481
      p22225
      (p22231 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p22234 (p22265 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p22227 p22228)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p22310 :=
nat_lit 2845889184420281923316526774158339737980764833991532348414548926717273466320081345851491521

noncomputable def p22311 :=
nat_lit 22538853009880653537648188844945783138936849921017987837241439655440807565623643931841

noncomputable def p22312 :=
nat_lit 8537622475554826008642505026097329322376016628274755009267972297272509517345112790266610881

noncomputable def p22313 :=
BSN.cos_dyadic_bound_f 46678455367 137438953472 3 2 137438953472
  68719476736 p22310 p2466 p22311
  p22312 p2469

noncomputable def p22314 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP 46678455367) (BSN.cosEvenQ 137438953472) 0
  2 p22310 p2466 p22311 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p22315 :=
p22313 p22311 129588143177 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p22314 (Eq.refl true))

noncomputable def p22316 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP 46678455367) (BSN.cosOddQ 137438953472) 0
  2 p22312 p2469 p22311 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p22317 :=
nat_lit 93421848385092114085609945199346643548931351384602905966121807767162918374400419199778816

noncomputable def p22318 :=
nat_lit 24288427909384612506985819240952793207490312938902921236780842594889675517512974336

noncomputable def p22319 :=
nat_lit 280265496578420523487604821626401448741207639173182840092522949739803565343850222573387776

noncomputable def p22320 :=
BSN.cos_dyadic_bound_f 19868950404 137438953472 3 2 137438953472
  68719476736 p22317 p2466 p22318
  p22319 p2469

noncomputable def p22321 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP 19868950404) (BSN.cosEvenQ 137438953472) 0
  2 p22317 p2466 p22318 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p22322 :=
p22320 p22318 136005269215 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p22321 (Eq.refl true))

noncomputable def p22323 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP 19868950404) (BSN.cosOddQ 137438953472) 0
  2 p22319 p2469 p22318 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p22324 :=
p22309 d113 d115 d117 d119 d103
  (p22315 (p22316 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p22322 (p22323 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p22325 :=
p22202 BSN.abs_quadSignPos (BSN.cos_quad_nat3 99 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 30422254713 137438953472)
  (Enclosure.sfrac_ofScientific_eq 102026600 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p22324 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p22224 433204801216492481 p22225 286700611133511
    137438953472 3341 137438953472
    (@p22229 p22222 p22223 433204801216492481
      p22225
      (p22231 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p22234 (p22265 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p22227 p22228)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p22326 :=
nat_lit
  923612370506649600350887833838551939860061394644455539734194217310598196374152263086663629269139600015733032769234656199787534393968554393761

noncomputable def p22327 :=
nat_lit
  47936522884622246504830455690021759272499892644479835485148718150757765900556949791231107530074531535846599049394041300089603716792481

noncomputable def p22328 :=
nat_lit
  5600985792196901695548624846678451910274006665182942710379192324372301997082422355723935149746511262384680744215311488198593332150319841788065

noncomputable def p22329 :=
BSN.cos_dyadic_bound_f 138056082009 137438953472 4 3 137438953472
  68719476736 p22326 p2457 p22327
  p22328 p2460

noncomputable def p22330 :=
@BSN.binarySplit_of_base3 (BSN.cosEvenP 138056082009) (BSN.cosEvenQ 137438953472) 0
  3 p22326 p2457 p22327 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p22331 :=
p22329 p22327 73738540868 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p22330 (Eq.refl true))

noncomputable def p22332 :=
@BSN.binarySplit_of_base3 (BSN.cosOddP 138056082009) (BSN.cosOddQ 137438953472) 0
  3 p22328 p2460 p22327 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p22333 :=
nat_lit 955509338232301831679470336007164531943828685114335971530203286743006547349504000000000000

noncomputable def p22334 :=
nat_lit 784200055172605009849540821474120419010870816278501642527681000000000000000000000000

noncomputable def p22335 :=
nat_lit 2502523187617844041609549218857434244610301491032415474528825468081493338296320000000000000

noncomputable def p22336 :=
BSN.sin_dyadic_bound_f 30676327000 137438953472 3 2 137438953472
  68719476736 p22333 p2477 p22334
  p22335 p2480

noncomputable def p22337 :=
@BSN.binarySplit_of_base2 (BSN.sinEvenP 30676327000) (BSN.sinEvenQ 137438953472) 0
  2 p22333 p2477 p22334 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p22338 :=
p22336 p22334 30422254713 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p22337 (Eq.refl true))

noncomputable def p22339 :=
@BSN.binarySplit_of_base2 (BSN.sinOddP 30676327000) (BSN.sinOddQ 137438953472) 0
  2 p22335 p2480 p22334 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p22340 :=
p22325 d121 d123 d125 d127 d103
  (p22331 (p22332 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p22338 (p22339 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p22341 :=
p22197 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 229 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 94401825900 137438953472)
  (Enclosure.sfrac_ofScientific_eq 102026600 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p22340 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p22224 433204801216492481 p22225 286700611133511
    137438953472 3341 137438953472
    (@p22229 p22222 p22223 433204801216492481
      p22225
      (p22231 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p22234 (p22265 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p22227 p22228)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p22342 :=
nat_lit
  1580251600827634000015802758158722557050859310303928233022899975707087876583953035562059163419619189183772458716914035945993014722497563590656

noncomputable def p22343 :=
nat_lit
  13675922064350103906721366741953497852162155536212421425380699349861653930918024219663747182281127028776106006506934443157188411129856

noncomputable def p22344 :=
nat_lit
  7900175650364819425590630514190225110871996612234481336207440212311647611800786142901603197759509232483980363167349651887606764382841330466816

noncomputable def p22345 :=
BSN.sin_dyadic_bound_f 124354942616 137438953472 4 3 137438953472
  68719476736 p22342 p2504 p22343
  p22344 p2507

noncomputable def p22346 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 124354942616) (BSN.sinEvenQ 137438953472) 0
  3 p22342 p2504 p22343 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p22347 :=
p22345 p22343 108068578983 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p22346 (Eq.refl true))

noncomputable def p22348 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 124354942616) (BSN.sinOddQ 137438953472) 0
  3 p22344 p2507 p22343 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p22349 :=
nat_lit
  774865274479921299868131455773285485918157461769378212988234683430657930029119308616076710101015910734029817810259460666691949021237153366016

noncomputable def p22350 :=
nat_lit
  1612885852235875037694155934525510410162289568331014113982557168106591510149830407550701291558379239993190978919905588864229379670016

noncomputable def p22351 :=
nat_lit
  3874066083252789297053427698124870872165457214600654315438654144422561374835627186865051278177812807633377240647620061497572996421244866789376

noncomputable def p22352 :=
BSN.sin_dyadic_bound_f 104063949072 137438953472 4 3 137438953472
  68719476736 p22349 p2504 p22350
  p22351 p2507

noncomputable def p22353 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 104063949072) (BSN.sinEvenQ 137438953472) 0
  3 p22349 p2504 p22350 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p22354 :=
p22352 p22350 94401825900 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p22353 (Eq.refl true))

noncomputable def p22355 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 104063949072) (BSN.sinOddQ 137438953472) 0
  3 p22351 p2507 p22350 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p22356 :=
p22341 d129 d131 d133 d135 d103
  (p22347 (p22348 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p22354 (p22355 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p22357 :=
p22192
  (p22356 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p22224 433204801216492481 p22225 286700611133511
    137438953472 3341 137438953472
    (@p22229 p22222 p22223 433204801216492481
      p22225
      (p22231 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p22234 (p22265 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p22227 p22228)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p22358 :=
nat_lit
  290496974501281402430023270301077149538357960728963019247932301638489814631431621496778837169515940846995412285255591509918833493765136237806293187211218623926911624520430019761854080000000000

noncomputable def p22359 :=
nat_lit
  21492196321247035358236385188899819980621385835421647366252974310216063843832658439250380634632050433741970712782015807357493962684178078095753323897390138244628906250000000000000000

noncomputable def p22360 :=
nat_lit
  2362561862215882954198843259113646757526823247276459110606824743369998162598511506322624829135731347012225385459699513982144360114915462911456339664529738162630990411324090007246526080000000000

noncomputable def p22361 :=
BSN.sin_dyadic_bound_f 215410837850 137438953472 5 4 137438953472
  68719476736 p22358 p20778 p22359
  p22360 p20781

noncomputable def p22362 :=
@BSN.binarySplit_of_base4 (BSN.sinEvenP 215410837850) (BSN.sinEvenQ 137438953472) 0
  4 p22358 p20778 p22359 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p22363 :=
p22361 p22359 137438123068 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p22362 (Eq.refl true))

noncomputable def p22364 :=
@BSN.binarySplit_of_base4 (BSN.sinOddP 215410837850) (BSN.sinOddQ 137438953472) 0
  4 p22360 p20781 p22359 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p22365 :=
p22357 d137 d139 d103
  (p22363 (p22364 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true) (Eq.refl true)

noncomputable def p22366 :=
@p22181 p20575 p22174 p22175
  (p22185
    (@p22188 218963 68719476736
      (p22365 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (p22365 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true) (Eq.refl true)))

noncomputable def p22367 :=
nat_lit
  53226291978642729694412274746191540564739121727832996118266749119648807890858841924918196854898171728794761905294859812684547561166998121472409619259582558620947059107446048223189548577860139089965951504626979892699051912491333353399505930514800263317043439343144144350368231267124738600235238220785523016958155868797

noncomputable def p22368 :=
nat_lit
  386051661123868214325895970762095083331216144111904370034983364157543830047598546775742309000849007597326427200921653578548066591998660043462778854257084865420374725869305346230443778499781067545394454342790117394565596548890481374012190543459242928201313126587598361115137891035519604744312911050121319319358268243968

noncomputable def p22369 :=
nat_lit
  108981502558006747384074072052631743132615399039264960983815103350757624352071957419332004737039213014599601897423476213725529137701041380931767985454637730657068227584537768699974339223784015622470426889127427850709056262296495086842071319915027007063548171196644116756464672334426016924924003482886586313415203

noncomputable def p22370 :=
@Enclosure.Real.IsNear.mulLit_ff p22169
  (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
        (Enclosure.sfrac false 12 1)))
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Zeta.RiemannSiegel.correctionLinear
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
          (Enclosure.sfrac false 12 1)))
      (@Inv.inv Real Real.instInv p22170)))

noncomputable def p22371 :=
nat_lit
  11059608304114582664653167427106952493806452651497028971934692611063469881128358233954882242113493634447249756040439913241455435472909456041911341853358830385807681322152760030843539621892978717765640880441685737936157850240761611083044661173211865777612927552054109505326157453044421318090222441250406646723

noncomputable def p22372 :=
nat_lit
  22471164185778948846616314884862809170224712236778832159178760144716584475687620391588559665300942002640014234983924169707348721101802077811605928829934265547220986678108185659537777450155761764931635369010625721104768835292807860184239138817603404645418813835573287279993405742309964538104419541203028017152

noncomputable def p22373 :=
nat_lit
  45284778281483116879903103055321124822328133552049209112829198536465481146794107161966586732783767023036720078385124929549475462634083653031843715278258422837562519046880520190763418753296762776012307555745549968896760444125241406420638299946041556803051169434269485335853251591353489366280445883844129

noncomputable def p22374 :=
@p22370 4812674239 17179869184 1 17179869184
  p22371 p22372 p22373 p20904
  p22367 p22368 p22369

noncomputable def p22375 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HPow.hPow Real Nat Real
    (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))
    (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)))
    12)
  (p22168
    (@Neg.neg Real Real.instNeg
      (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
        (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))
        (@OfNat.ofNat Real 4
          (@instOfNatAtLeastTwo Real 4 Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 3 (instOfNatNat 3))
              (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 2 (instOfNatNat 2)))))))))

noncomputable def p22376 :=
@p22375 1 1 0 1 4812674239 17179869184
  1 17179869184 4812674239 17179869184 1

noncomputable def p22377 :=
@Enclosure.Real.IsNear.of_eq
  (p22168
    (@Neg.neg Real Real.instNeg
      (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
        (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))
        (@OfNat.ofNat Real 4
          (@instOfNatAtLeastTwo Real 4 Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 3 (instOfNatNat 3))
              (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 2 (instOfNatNat 2)))))))))

noncomputable def p22378 :=
BSN.rpow_neg_quarter_mk
  (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
      true 5)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@OfNat.ofNat Real 2
        (@instOfNatAtLeastTwo Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p22379 :=
p22378
  (BSN.t_div_two_pi_nonneg
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
      true 5)
    102026600 100000
    (Enclosure.sfrac_ofScientific_eq 102026600 5 100000 (Eq.refl true)))

noncomputable def p22380 :=
@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt p22170)) false
  4812674239 17179869184 1 17179869184 4812674239
  17179869184

noncomputable def p22381 :=
@Enclosure.Real.IsNear.recentre' (Real.sqrt p22170) false 61327214459
  17179869184 7 17179869184 61327214459 17179869184 7
  17179869184

noncomputable def p22382 :=
@Enclosure.Real.IsNear.sqrt_image
  (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
      true 5)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@OfNat.ofNat Real 2
        (@instOfNatAtLeastTwo Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p22383 :=
@Enclosure.Real.IsNear.of_eq
  (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
      true 5)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@OfNat.ofNat Real 2
        (@instOfNatAtLeastTwo Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p22384 :=
@p22383
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 102026600 100000)
    (@Inv.inv Real Real.instInv
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)))
  false 1394836819256699

noncomputable def p22385 :=
@p22384 8589934592000 510133 8589934592000
  (BSN.t_div_two_pi_mk
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
      true 5)
    102026600 100000
    (Enclosure.sfrac_ofScientific_eq 102026600 5 100000 (Eq.refl true)))

noncomputable def p22386 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 102026600 100000)
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi))
  102026600 100000 0

noncomputable def p22387 :=
@p22386 1 2734261103 17179869184 1 17179869184
  1394836819256699 8589934592000 510133 8589934592000
  (Enclosure.Real.IsNear.const false 102026600 100000) d261

noncomputable def p22388 :=
@p22382 1394836819256699 8589934592000 510133 8589934592000
  109460298919 109460298960 8589934592
  (p22385 (p22387 (Eq.refl true))) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p22389 :=
@Enclosure.Real.IsNear.recentre' p22170 false 218920597879 17179869184
  41 17179869184 218920597879 17179869184 41 17179869184
  (p22388 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p22390 :=
@Enclosure.Real.IsNear.sqrt_image p22170 218920597879 17179869184 41
  17179869184 30663607226 30663607233 8589934592
  (p22389 (Eq.refl true)) (Eq.refl true) (Eq.refl true)

noncomputable def p22391 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt p22170) 61327214459 17179869184
  7 17179869184 2406337119 2406337120 8589934592
  (p22381
    (p22390 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p22392 :=
@p22377 (@Inv.inv Real Real.instInv (Real.sqrt p22170)) false
  4812674239 17179869184 1 17179869184 p22379
  (@p22380 1 17179869184
    (p22391 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p22393 :=
@Enclosure.Real.IsNear.recentre'
  (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
        (Enclosure.sfrac false 12 1)))
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Zeta.RiemannSiegel.correctionLinear
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
          (Enclosure.sfrac false 12 1)))
      (@Inv.inv Real Real.instInv p22170)))

noncomputable def p22394 :=
nat_lit
  19246030769630324673958818798511478049489456759620913872952409377997829487387495543835799361433100984790606033313678095058527071619485552538533578993259829705964070594924221081074452970151124179805230711191858736781123188753227597728771277477067661641296747009564531267737631926325232980669189500633754820843719

noncomputable def p22395 :=
nat_lit
  19100489557912106519623867652133387794691005401262007335301946123009096804334477332850275715505800702244012099736335544251246412936531766139865039505444125715137838676391957810607110832632397500191890063659031862939053509998886681156603267994962893948605991760237294187994394880963469857388756610022573814579200000000

noncomputable def p22396 :=
@Enclosure.Real.IsNear.addLit_ft_p
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
      (Enclosure.sfrac false 12 1)))
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Zeta.RiemannSiegel.correctionLinear
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
        (Enclosure.sfrac false 12 1)))
    (@Inv.inv Real Real.instInv p22170))
  72751193364532353111

noncomputable def p22397 :=
nat_lit 979983278915819929600000000

noncomputable def p22398 :=
nat_lit
  18254571533038924032016549886221506131467497950319138874447141898404631607785646743644675529832967564979633382115425996043587865874033300790075241367713107403979897723283838296421614731507968971467425889638054035253254194459373250143960956001585655629723948812548112520744176499354917933934897891575741501

noncomputable def p22399 :=
nat_lit
  3891183930960477314760193744817361915472481691619001979118819034645934991879556887763047405308859544595705494909234570632628795616742757876345385748828934889805101995725659006053516371647989467464330515707506734930378553344236123760289459822200258841437676863496363879983034433094149343854917197140023

noncomputable def p22400 :=
nat_lit
  2876309015779705452366888305262439573788763166307690516374881298523722812888015410123335637158520576337921822077942293722540636301030665959885558890231585990044286294797847764420835513619937505911249327233360092301410410917479406103582609768653235794613608170953380771839155935015675460877365701273987586195456

noncomputable def p22401 :=
nat_lit
  1632110111531796977812567075324256611837112400039788417881942207939576296361295210697199406699597059684354925856939521992428417391959207701908549709449143967219114735003311787575206953513921676673061341940627091235164095883503553437772028836047816487536621941455303142877753395582056723064590174107386375090127969756947566034944

noncomputable def p22402 :=
@p22396 147573952589676412928 986124759748898165097 p22397
  p22398 p22372 p22399 p22400
  p22401 p22371 p22372 p22394

noncomputable def p22403 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  (@Inv.inv Real Real.instInv
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
          (Enclosure.sfrac false 12 1)))))

noncomputable def p22404 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
        (Enclosure.sfrac false 12 1))
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
        (Enclosure.sfrac false 12 1)))
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
      (Enclosure.sfrac false 12 1)))

noncomputable def p22405 :=
@Enclosure.Real.IsNear.of_eq
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
      (Enclosure.sfrac false 12 1)))
  (p22403
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p22404 (Enclosure.sfrac false 1 16)))))

noncomputable def p22406 :=
BSN.cos_two_pi_p_ne_zero_mk
  (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
    true 5)
  102026600 100000 12
  (Enclosure.sfrac_ofScientific_eq 102026600 5 100000 (Eq.refl true))

noncomputable def p22407 :=
@Enclosure.Real.IsNear.mulLit_tt
  (@Inv.inv Real Real.instInv
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
          (Enclosure.sfrac false 12 1)))))

noncomputable def p22408 :=
@p22407
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p22404 (Enclosure.sfrac false 1 16))))
  382860033549

noncomputable def p22409 :=
@p22408 17179869184 130643 17179869184 190020339
  8589934592 4290195057 114085068800000000 72751193364532353111
  147573952589676412928 986124759748898165097 p22397

noncomputable def p22410 :=
@Enclosure.Real.IsNear.of_eq
  (@Inv.inv Real Real.instInv
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
          (Enclosure.sfrac false 12 1)))))

noncomputable def p22411 :=
@Inv.inv Real Real.instInv
  (@Neg.neg Real Real.instNeg
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
          (Enclosure.sfrac false 12 1)))))

noncomputable def p22412 :=
@p22410 (@Neg.neg Real Real.instNeg p22411) true 382860033549
  17179869184 130643 17179869184
  (BSN.inv_eq_neg_inv_neg
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
          (Enclosure.sfrac false 12 1)))))

noncomputable def p22413 :=
@Enclosure.Real.IsNear.inv_image
  (@Neg.neg Real Real.instNeg
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
          (Enclosure.sfrac false 12 1)))))

noncomputable def p22414 :=
@Enclosure.Real.IsNear.neg
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
        (Enclosure.sfrac false 12 1))))
  true

noncomputable def p22415 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
        (Enclosure.sfrac false 12 1))))
  true

noncomputable def p22416 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
      (Enclosure.sfrac false 12 1)))
  (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
    (@Nat.cast Real Real.instNatCast 40093532199)
    (@Nat.cast Real Real.instNatCast 8589934592))
  false

noncomputable def p22417 :=
nat_lit 11285326041988133955070405

noncomputable def p22418 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
      (Enclosure.sfrac false 12 1)))
  false p22417

noncomputable def p22419 :=
nat_lit 1106429201396991409688902879

noncomputable def p22420 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
    (Enclosure.sfrac false 12 1))
  884279719003555 140737488355328 1

noncomputable def p22421 :=
@Enclosure.Real.IsNear.subLit_ff_p p22170 (Enclosure.sfrac false 12 1)
  218920597879 17179869184 41 17179869184 12 1 0

noncomputable def p22422 :=
@p22420 500000000000000 12762167671 17179869184 41
  17179869184 p22417 p2602 p22419
  p5018 d260
  (@p22421 1 12762167671 12762167671 17179869184 41
    17179869184 (p22389 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p22423 :=
@p22416 40093532199 8589934592 129 8589934592 true
  770902887 17179869184 1 3400000000
  (@p22418 p2602 p22419 p5018
    40093532199 8589934592 129 8589934592
    (p22422 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div 40093532199 8589934592)

noncomputable def p22424 :=
nat_lit 1888983600480657703392247808

noncomputable def p22425 :=
BSN.cos_reduce2
  (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
    (@Nat.cast Real Real.instNatCast 40093532199)
    (@Nat.cast Real Real.instNatCast 8589934592))
  (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
    (@Nat.cast Real Real.instNatCast p22424)
    (@Nat.cast Real Real.instNatCast p2445))
  226375608064910080 72057594037927936 false

noncomputable def p22426 :=
BSN.sin_reduce_arg_pos_rat_q2 40093532199 8589934592 226375608064910080
  72057594037927936 0 p22424 p2445 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p22427 :=
nat_lit
  26152873324273403874465001494748138863821568948922079264759680315726052743140637284193948759068314098623572791022999239018009316773212592338368929676894943100378299887217130943468142128352008107435636118239432513518820099736073921

noncomputable def p22428 :=
nat_lit
  4764903642034301360822552556740905586108042196302286662534793003311882585794366454137024705198434081192212921773724267015243926811547612080829008368818939869808353974932699813835782357521565102389912701194613280347125441

noncomputable def p22429 :=
nat_lit
  266186931495568858712924709150399377210270278510170243949852499647942966292458651288913948692338996840015007119210061869347884947527357238274562273109733978179960909140640168074642507157688292906036621856523630751112866235605186241

noncomputable def p22430 :=
BSN.cos_dyadic_bound_f 53688143011659 35184372088832 5 4 17179869184
  6806640626 p22427 p12328 p22428
  p22429 p12330

noncomputable def p22431 :=
@BSN.binarySplit_of_base4 (BSN.cosEvenP 53688143011659) (BSN.cosEvenQ 35184372088832) 0
  4 p22427 p12328 p22428 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p22432 :=
p22430 p22428 770902887 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p22431 (Eq.refl true))

noncomputable def p22433 :=
@BSN.binarySplit_of_base4 (BSN.cosOddP 53688143011659) (BSN.cosOddQ 35184372088832) 0
  4 p22429 p12330 p22428 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p22434 :=
@BSN.cos_arg_round false 770902887 17179869184 p22424 p2445
  53688143011659 35184372088832 6806640626 6800000000
  (p22432 (p22433 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p22435 :=
p22425 770902887 17179869184 0 1000000000000000
  6800000000 3400000000 p22426 BSN.pi_near_15 p22434
  (Eq.refl true) (Eq.refl true)

noncomputable def p22436 :=
@p22414 770902887 17179869184 873417841 57042534400000000
  (@p22415 770902887 17179869184 447189934592
    29205777612800000000 770902887 17179869184 873417841
    57042534400000000
    (p22423 (p22435 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p22437 :=
@p22413 770902887 17179869184 873417841 57042534400000000
  191429951453 191430082096 8589934592 p22436
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p22438 :=
@Enclosure.Real.IsNear.recentre' p22411 false 382860033549 17179869184
  130643 17179869184 382860033549 17179869184 130643
  17179869184
  (p22437 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p22439 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p22404 (Enclosure.sfrac false 1 16))))
  true

noncomputable def p22440 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p22404 (Enclosure.sfrac false 1 16)))
  (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
    (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 1710384193))
    (@Nat.cast Real Real.instNatCast 1073741824))
  true

noncomputable def p22441 :=
nat_lit 66167283596419656667155715550017645

noncomputable def p22442 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p22404 (Enclosure.sfrac false 1 16)))
  true p22441

noncomputable def p22443 :=
nat_lit 47249174916612600659892844775348790537

noncomputable def p22444 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (p22404 (Enclosure.sfrac false 1 16)) 884279719003555
  140737488355328 1

noncomputable def p22445 :=
@Enclosure.Real.IsNear.subLit_tf
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
        (Enclosure.sfrac false 12 1))
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
        (Enclosure.sfrac false 12 1)))
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
      (Enclosure.sfrac false 12 1)))

noncomputable def p22446 :=
@p22445 (Enclosure.sfrac false 1 16) 56379447429336386223
  295147905179352825856 1750872387247 295147905179352825856 1 16
  0

noncomputable def p22447 :=
@Enclosure.Real.IsNear.subLit_ff_n
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
      (Enclosure.sfrac false 12 1))
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
      (Enclosure.sfrac false 12 1)))
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
    (Enclosure.sfrac false 12 1))
  162872923662717564241

noncomputable def p22448 :=
nat_lit 968591531502204199242439852032

noncomputable def p22449 :=
@p22447 295147905179352825856 1046497750703 295147905179352825856
  12762167671 17179869184 41 17179869184 p22448
  56379447429336386223 295147905179352825856 1750872387247

noncomputable def p22450 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
    (Enclosure.sfrac false 12 1))
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
    (Enclosure.sfrac false 12 1))
  12762167671 17179869184 41

noncomputable def p22451 :=
@p22450 17179869184 12762167671 17179869184 41
  17179869184 162872923662717564241 295147905179352825856 1046497750703
  295147905179352825856
  (@p22421 1 12762167671 12762167671 17179869184 41
    17179869184 (p22389 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p22452 :=
p22451
  (@p22421 1 12762167671 12762167671 17179869184 41
    17179869184 (p22389 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p22453 :=
@p22449 295147905179352825856 (p22452 (Eq.refl true))
  (@p22421 1 12762167671 12762167671 17179869184 41
    17179869184 (p22389 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p22454 :=
@p22444 500000000000000 74826191503045937839 295147905179352825856
  1750872387247 295147905179352825856 p22441 p2630
  p22443 p2632 d260
  (@p22446 1 1197219064048735005424 74826191503045937839
    295147905179352825856 1750872387247 295147905179352825856
    (p22453 (Eq.refl true) (Eq.refl true))
    (Enclosure.Real.IsNear.const false 1 16) (Eq.refl true)
    (Eq.refl true))

noncomputable def p22455 :=
@p22440 1710384193 1073741824 641 17179869184 true
  190020339 8589934592 1 3400000000
  (@p22442 p2630 p22443 p2632
    1710384193 1073741824 641 17179869184
    (p22454 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_true_div 1710384193 1073741824)

noncomputable def p22456 :=
nat_lit
  17589098338822363961766147079697318443082867360762647101864601105544555348411755474194226348937659514178603021763657206867925394717543409685854298261277230081

noncomputable def p22457 :=
nat_lit
  5364123740152539918651790787530588473940179442204010661777428824111901034111223916227944991510617075914948388501268079941300329833612722381292160001

noncomputable def p22458 :=
nat_lit
  178951871515769310870147694269123186404236278070678590808316802763334546840095123254768029179796708387980018233500381700549814483247657593314298855676897510401

noncomputable def p22459 :=
BSN.cos_dyadic_bound_t 1710384193 1073741824 5 4 8589934592
  3400000000 p22456 p9466 p22457
  p22458 p9469

noncomputable def p22460 :=
@BSN.binarySplit_of_base4 (BSN.cosEvenP 1710384193) (BSN.cosEvenQ 1073741824) 0
  4 p22456 p9466 p22457 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p22461 :=
p22459 p22457 190020339 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p22460 (Eq.refl true))

noncomputable def p22462 :=
@BSN.binarySplit_of_base4 (BSN.cosOddP 1710384193) (BSN.cosOddQ 1073741824) 0 4
  p22458 p9469 p22457 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p22463 :=
p22455
  (BSN.cos_neg_of_bound 1710384193 1073741824 true 190020339 8589934592
    1 3400000000
    (p22461 (p22462 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p22464 :=
p22409
  (p22412
    (@Enclosure.Real.IsNear.neg p22411 false 382860033549 17179869184
      130643 17179869184 (p22438 (Eq.refl true))))
  (@p22439 190020339 8589934592 2196579869184
    58411555225600000000 190020339 8589934592 4290195057
    114085068800000000 (p22463 (Eq.refl true)) (Eq.refl true))

noncomputable def p22465 :=
@p22402 p22395
  (@p22405 false 72751193364532353111 147573952589676412928
    986124759748898165097 p22397
    (BSN.correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
        (Enclosure.sfrac false 12 1))
      (p22406 (Eq.refl true) (Eq.refl true)
        (p22173 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p22464 (Eq.refl true)))

noncomputable def p22466 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Zeta.RiemannSiegel.correctionLinear
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
        (Enclosure.sfrac false 12 1)))
    (@Inv.inv Real Real.instInv p22170))
  true

noncomputable def p22467 :=
nat_lit
  133700061809567775483559441732914711359601802027698966339796821215572653835717779231310649624793668184768069141461255754077941661454226360989998750333797965201810215084688297752381750736229571095294044891988445825805733788106284653218014187438848691893677374007461912635542415399850172166373823444035067974707871

noncomputable def p22468 :=
nat_lit
  13539996872783604883509713210358095908143901110839286161735973918949699476840177918625770291262810820476627801084490714354883964820689470279440030950001886560792268076432536159011016433036926317286815234726334997908330457429616133387197520543552464915209951496625825545026668711815366287964250961

noncomputable def p22469 :=
nat_lit
  1307993905256673975767120421215822522657964858038981454399109360803651185455244290152830052265253733065911465963809993683089776960073625541502023629723947119620918917825223508962533521125777727280023703876104306028269279939868013618062200188730110219063866757530095479450736063434158250346338582528

noncomputable def p22470 :=
@Enclosure.Real.IsNear.mulLit_tf
  (Zeta.RiemannSiegel.correctionLinear
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
      (Enclosure.sfrac false 12 1)))
  (@Inv.inv Real Real.instInv p22170) p22468 p22469

noncomputable def p22471 :=
nat_lit
  198250845126006999773136496310174725773185767097319083749901341058746939467004635580340396694809641794309076918984865242826289706713378168074123548716898072277615677473844372652893679635578058538400863774200086968271348642088561665068061932925605422196312820353848062502875738239968256720688385489697337

noncomputable def p22472 :=
nat_lit
  11505236063118821809467553221049758295155052665230762065499525194094891251552061640493342548634082305351687288311769174890162545204122663839542235560926343960177145179191391057683342054479750023644997308933440369205641643669917624414330439074612943178454432683813523087356623740062701843509462805095950344781824

noncomputable def p22473 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  (@iteratedDeriv Real (@DenselyNormedField.toNontriviallyNormedField Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal Real Real.instRCLike))
    (@OfNat.ofNat Nat 3 (instOfNatNat 3)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
      (Enclosure.sfrac false 12 1)))
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 96 1)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) Real.pi Real.pi)))

noncomputable def p22474 :=
@Enclosure.Real.IsNear.of_eq
  (Zeta.RiemannSiegel.correctionLinear
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
      (Enclosure.sfrac false 12 1)))
  (@Neg.neg Real Real.instNeg p22473) true p22468

noncomputable def p22475 :=
nat_lit
  13950663003677672457710807793602152353654393789082145816289465189562124201998361901432176383621102050542096290332482563881468115343038724137922591876752015081436013651673833077765162824497708392081084744472010786227506906260838506285410412396839254250839016328483644640506924264530251983970120864322207862773596909543

noncomputable def p22476 :=
nat_lit
  809609013229242473409981386875669228198226599056568473427605432109721358271981387567841534805748497980748311457267247645559234949543173907468053599762954039686069697106265445457867630968372865364959070713890980274248029933698770794472413422596638225363240226049435078209333658460922010128745310034584025053230830964373979136

noncomputable def p22477 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@iteratedDeriv Real (@DenselyNormedField.toNontriviallyNormedField Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal Real Real.instRCLike))
    (@OfNat.ofNat Nat 3 (instOfNatNat 3)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
      (Enclosure.sfrac false 12 1)))
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 96 1)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) Real.pi Real.pi)))

noncomputable def p22478 :=
nat_lit
  712147209077113477959136148511987778066248460900043956722384949965747971862891902551342689596692517602163968733220449355938353274156616925642664769965431665178250294066640317524953742046358059421408032301625150261646191788356559582573731470736918596408898446566731849411009723108189

noncomputable def p22479 :=
nat_lit
  72608247484266751113186645417475613287659189534150120071082610318161164900410369802010171606257634306142515810068016262229227795192622349013224149467890362587059123068723626657357734855190319183117148231560128769827526792328021488679545846696711820459572514914753120743347917422592

noncomputable def p22480 :=
nat_lit
  1467493013813157452266173945774465163414860526655028214702350620097341532828071686680357483262189867182514847870741649317995167954104686440795754927085913802471298483809207674901970214401997513902194759439075737472964437951242800040766705869491790509862560491312715071652308559242547570628962953333206925

noncomputable def p22481 :=
@p22477 p22478 p22479 p22480
  p20924 19012918537349 18014398509481984 1 18014398509481984
  p22468 p22469 p22475

noncomputable def p22482 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p22483 :=
p22482
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p22484 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p22483
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p22485 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p22484
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p22404 (Enclosure.sfrac false 1 16)))))

noncomputable def p22486 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  (Enclosure.sfrac false 3 1)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p22487 :=
p22485
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p22486
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 4 1) Real.pi))
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p22404 (Enclosure.sfrac false 1 16)))))

noncomputable def p22488 :=
@Neg.neg Real Real.instNeg
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
          (Enclosure.sfrac false 12 1)))))

noncomputable def p22489 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22487
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 3 1) p22488)
    (@iteratedDeriv Real (@DenselyNormedField.toNontriviallyNormedField Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal Real Real.instRCLike))
      (@OfNat.ofNat Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
        (Enclosure.sfrac false 12 1))))

noncomputable def p22490 :=
@Neg.neg Real Real.instNeg
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 4 1)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) Real.pi Real.pi))
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
          (Enclosure.sfrac false 12 1)))))

noncomputable def p22491 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22489
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 3 1) p22490)
    (@iteratedDeriv Real (@DenselyNormedField.toNontriviallyNormedField Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal Real Real.instRCLike))
      (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
        (Enclosure.sfrac false 12 1))))

noncomputable def p22492 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 8 1)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) Real.pi Real.pi) Real.pi))
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
        (Enclosure.sfrac false 12 1))))

noncomputable def p22493 :=
@Enclosure.Real.IsNear.of_eq
  (@iteratedDeriv Real (@DenselyNormedField.toNontriviallyNormedField Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal Real Real.instRCLike))
    (@OfNat.ofNat Nat 3 (instOfNatNat 3)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
      (Enclosure.sfrac false 12 1)))
  (p22403
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22491
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p22492
        (Zeta.RiemannSiegel.correction
          (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
            (Enclosure.sfrac false 12 1))))))

noncomputable def p22494 :=
@Enclosure.Real.IsNear.recentre'
  (p22403
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22491
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p22492
        (Zeta.RiemannSiegel.correction
          (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
            (Enclosure.sfrac false 12 1))))))

noncomputable def p22495 :=
nat_lit
  6609000990177742041363930870341807918293316159285160791091563502127968126279696551809588077474582755165061706824286857158606140891628156720043689380376597615229514250049219426911426525866426388219934104001883770101132369772265150853216173791765839877602397666682919548840010784280538353579480616755997372105636333915533

noncomputable def p22496 :=
@p22407
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22491
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p22492
      (Zeta.RiemannSiegel.correction
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
          (Enclosure.sfrac false 12 1)))))
  401457751629956851

noncomputable def p22497 :=
nat_lit
  1773903246819192624367194735027556897474148704489452951019196055400205697489090892179228056071796914411358206953948473323218190905484797071228108829316262284289240743456771483771967634778016096001920083582946900068884621736323930612646100899548655360999519458941039

noncomputable def p22498 :=
nat_lit
  4030567406735727282351225165683873035574701889313671280883489296162978382543372035785043761349923613698382530160958318167742519832631573007587730243400112738864034149162331269597866193210040596412843573823632724030670381872189039145190406026970187961498554846937088

noncomputable def p22499 :=
nat_lit
  32925007283102207948947911658688206064025715254635328734200752971824964997759076859415600574917125626671374089648817922135202138973651269697155104993636072360904724678271348618402598194770950811453343366804802086203787140971289451229564930622441290275694411368538011433769912161860848734594007652098575

noncomputable def p22500 :=
@p22496 18014398509481984 130643 18014398509481984
  p22497 p22498 p22499 p20904
  p22478 p22479 p22495 p20899

noncomputable def p22501 :=
@p22410 (@Neg.neg Real Real.instNeg p22411) true
  401457751629956851 18014398509481984 130643 18014398509481984
  (BSN.inv_eq_neg_inv_neg
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
          (Enclosure.sfrac false 12 1)))))

noncomputable def p22502 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
      (Enclosure.sfrac false 12 1)))
  (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
    (@Nat.cast Real Real.instNatCast 84082231055500187)
    (@Nat.cast Real Real.instNatCast 18014398509481984))
  false

noncomputable def p22503 :=
nat_lit 62917794999320994409728634700413698696341716523755908196190965420219

noncomputable def p22504 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
      (Enclosure.sfrac false 12 1)))
  false p22503

noncomputable def p22505 :=
nat_lit 17121160916665483071190193476420586781587190312313680939706815045155349005262625382539493

noncomputable def p22506 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
    (Enclosure.sfrac false 12 1))
  p20538 p20539 1

noncomputable def p22507 :=
@Enclosure.Real.IsNear.subLit_ff_p p22170 (Enclosure.sfrac false 12 1)
  229554884812461535 18014398509481984 41 18014398509481984 12
  1 0

noncomputable def p22508 :=
@p22383
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 102026600 100000)
    (@Inv.inv Real Real.instInv
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)))
  false 1462592412217536096757

noncomputable def p22509 :=
@p22508 9007199254740992000 510133 9007199254740992000
  (BSN.t_div_two_pi_mk
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
      true 5)
    102026600 100000
    (Enclosure.sfrac_ofScientific_eq 102026600 5 100000 (Eq.refl true)))

noncomputable def p22510 :=
@p22386 1 2867080569611329 18014398509481984 1
  18014398509481984 1462592412217536096757 9007199254740992000 510133
  9007199254740992000 (Enclosure.Real.IsNear.const false 102026600 100000)
  d264

noncomputable def p22511 :=
@p22382 1462592412217536096757 9007199254740992000 510133
  9007199254740992000 114777442406230747 114777442406230788 9007199254740992
  (p22509 (p22510 (Eq.refl true))) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p22512 :=
@Enclosure.Real.IsNear.recentre' p22170 false 229554884812461535
  18014398509481984 41 18014398509481984 229554884812461535
  18014398509481984 41 18014398509481984
  (p22511 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p22513 :=
@p22506 p20541 13382102698677727 18014398509481984 41
  18014398509481984 p22503 p16711 p22505
  p20932 d263
  (@p22507 1 13382102698677727 13382102698677727
    18014398509481984 41 18014398509481984
    (p22512 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p22514 :=
@p22502 84082231055500187 18014398509481984 129
  9007199254740992 true 808350448685697 18014398509481984 1
  3565158400000000
  (@p22504 p16711 p22505 p20932
    84082231055500187 18014398509481984 129 9007199254740992
    (p22513 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div 84082231055500187 18014398509481984)

noncomputable def p22515 :=
nat_lit 329107356863591261644679366579658698754984905253553465686467564011520

noncomputable def p22516 :=
BSN.cos_reduce2
  (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
    (@Nat.cast Real Real.instNatCast 84082231055500187)
    (@Nat.cast Real Real.instNatCast 18014398509481984))
  (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
    (@Nat.cast Real Real.instNatCast p22515)
    (@Nat.cast Real Real.instNatCast p14600))
  p2138 p2102 false

noncomputable def p22517 :=
BSN.sin_reduce_arg_pos_rat_q2 84082231055500187 18014398509481984 p2138
  p2102 0 p22515 p14600 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p22518 :=
nat_lit
  12034329737029497011924126214166324818482118224703056812216412718162794767934948853550262809390861853389174883742459317547805975466421141538819573681248620801003573756482428719684233622597858903693506866041070968275405690614315053310645082102090241469367613211197260403161573846849627892730588331292090879800642495923721135857327638184762280404399858614741724773482380754836224318380308969166581229029147523681

noncomputable def p22519 :=
nat_lit
  102227057692627802517266515998174650690372626538432533070010301911899107676238467813500602425144517548694181231874769092268404531268036906608629786628087536905891441490871663203598820654535688857960482672455898926949423622927541910197421361409963215519630902849946112116191457711434812050222994656178611158063212643599685778334824076798440559210627041367520318035583955510393566193592317724834401

noncomputable def p22520 :=
nat_lit
  184931024493475743929599416310582786928961597322994545720774116986063376657554345476778188315734359452963300030571320959933977272006220415821369068439594935612741272117143713893704845383866308267477160824547770951802927386429418258026323402083600838207181378962802755223340147314453258687553188961051003762535723080543319649743418978863414265753832081076238855007194841158456936920212299738536498008421527960161

noncomputable def p22521 :=
BSN.cos_dyadic_bound_f 56296097872430417497 36893488147419103232 6 5
  18014398509481984 7137280000000001 p22518 p20947
  p22519 p22520 p20950

noncomputable def p22522 :=
@BSN.binarySplit_of_base5 (BSN.cosEvenP 56296097872430417497) (BSN.cosEvenQ 36893488147419103232)
  0 5 p22518 p20947 p22519
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p22523 :=
p22521 p22519 808350448685697 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p22522 (Eq.refl true))

noncomputable def p22524 :=
@BSN.binarySplit_of_base5 (BSN.cosOddP 56296097872430417497) (BSN.cosOddQ 36893488147419103232)
  0 5 p22520 p20950 p22519
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p22525 :=
@BSN.cos_arg_round false 808350448685697 18014398509481984 p22515
  p14600 56296097872430417497 36893488147419103232 7137280000000001
  7130316800000000
  (p22523 (p22524 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p22526 :=
p22516 808350448685697 18014398509481984 0 p2139
  7130316800000000 3565158400000000 p22517 d102
  p22525 (Eq.refl true) (Eq.refl true)

noncomputable def p22527 :=
@p22414 808350448685697 18014398509481984 873417841
  59813432551014400000000
  (@p22415 808350448685697 18014398509481984 468912632854740992
    p20927 808350448685697 18014398509481984 873417841
    59813432551014400000000
    (p22514 (p22526 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p22528 :=
@p22413 808350448685697 18014398509481984 873417841
  59813432551014400000000 200728875814913104 200728875815043747 9007199254740992
  p22527 (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p22529 :=
@Enclosure.Real.IsNear.recentre' p22411 false 401457751629956851
  18014398509481984 130643 18014398509481984 401457751629956851
  18014398509481984 130643 18014398509481984
  (p22528 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p22530 :=
nat_lit
  494151776115048597386111634717579270289953109797778224481565332208287592529519404509462610370674832462624036570461239375147748003145696758613908885389595944657992185067165556481571523322019838947031152727266370877130583170684972928455148004365800213000074241405343855

noncomputable def p22531 :=
@Enclosure.Real.IsNear.subLit_tt_n p22491
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p22492
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
        (Enclosure.sfrac false 12 1))))
  p22530 p22498

noncomputable def p22532 :=
nat_lit
  131656958674288559571216230366547885789351957805384462105822463687531567928172583020819035797895061938030854687201761574587761810486755253777522937551893294583788882627748784979856201883361205078346058098801878019151003369707702121740634630874334332944391063186964394821890867284345713002092617406224943

noncomputable def p22533 :=
nat_lit
  37403259586667022897639919472929482890219498287005568552422088298310309516196251452106478181266345038682074782430319201923140568337920443023665901620844381366289071793986292397785575714299514880714655973

noncomputable def p22534 :=
nat_lit
  43070458120272224575416268204938466750903213156852830980548199768292062863724416843366501773440568654641671393510113953046745407849825011097482422650994859830016085336609493754190895722598167467315368417330325664145194177455683177625091615430828158386582287187650913188781363097681936283413202169357

noncomputable def p22535 :=
nat_lit
  543134063160213451147586364671648695171045522742024033015306221820515685620357281505275014683299128275281459577233390662410652027366249064063213701243341671238782448403165469792698826797874371649975708172354969815486996462222609057991546220318166885010044627263055348318926136723567370534649396549950896900191387649491858222805701858137000730314368331357219089846460274969654714131699454944507666639487941548932828825554303496523742255645916233626090409399571972096

noncomputable def p22536 :=
@p22531 p22532 p20578 p22533
  p21002 p22534 p20578 p22535
  p22497 p22498 p22499 p20904

noncomputable def p22537 :=
@Enclosure.Real.IsNear.subLit_tf p22489
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 3 1) p22490)
    (@iteratedDeriv Real (@DenselyNormedField.toNontriviallyNormedField Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal Real Real.instRCLike))
      (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
        (Enclosure.sfrac false 12 1))))

noncomputable def p22538 :=
nat_lit
  473481181259657221648114536896064441586756814823913971741915454451159302496416543884205432771532141518737279295291816825840213067485404351217682516097783027724586191855194644210829801126899161906417921797200442241978836847854585384057997509557754238980584428626761839

noncomputable def p22539 :=
nat_lit
  32881052055937066867376000333589254218281881516541308083636739853099146047704624949898591976339288614018116364853765303863054075252937283192811200677364716195739099859470480785945595572354852487511224186927953919336602204199475347482260999380078141461243718371099840225987862388991531743936277039684395

noncomputable def p22540 :=
nat_lit
  509569505283775946306120930359177973320557242817402655961236579308620457031903736051003134024686200185509484456881236047023907968686405369156136898267470603799031667395582518347027673294827277222116540818092654323583246981701727110813

noncomputable def p22541 :=
nat_lit
  99361157907245371849534687261600163536440705095468583112899330433667260971928120725176218165033374588831214764616388685194981122823348121052434385602635592909085118465334393955216978280422300468816831948397854000057142198644227702784

noncomputable def p22542 :=
nat_lit
  132750450540292101712229032190868916224431739219229771275504275134983737354083221224667892537907481958389227786700359135545509475006121006278134842434429800832483189866861836073819593941795128301161351090062341804594552909800731811590633354021767099416189702565033917939417728379586026347509247487363

noncomputable def p22543 :=
nat_lit
  49099492656713105619116505756954596435710864540693084046255229035995508786928983909221800528803081818704052675229654027179003657185371315610342016235778185808194220464076462741100975164223666124804172448296141725410033075242303489759615494909163745875802304252710128875628173710490852705461542740324678344309755107835852167153641525922921507852019464357912165811509812623587995618237454945763402127545826865241956432276548997944955926862430636682362715194769560960555104439189678182509417488260792320

noncomputable def p22544 :=
@p22537 p22538 p22498 p22539
  p20904 p22540 p22541 p22542
  p20578 p22543 p22530 p22498

noncomputable def p22545 :=
@Enclosure.Real.IsNear.subLit_tf p22487
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 3 1) p22488)
    (@iteratedDeriv Real (@DenselyNormedField.toNontriviallyNormedField Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal Real Real.instRCLike))
      (@OfNat.ofNat Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
        (Enclosure.sfrac false 12 1))))

noncomputable def p22546 :=
nat_lit
  35674345776569893693707338545404655173551384266393009614858145351513149587970835058783920385733604010100552147783669046130860428751520149943903446358876722987966754748770163791418348019139045873246131377028445833028495

noncomputable def p22547 :=
nat_lit
  1378913065775496824682182051857728448902028277271278088224317349054049721856053955032165000485952146958446223387833982704161766047792183079895777875237766653530662154044294980748355504146827894396365898183024673030144

noncomputable def p22548 :=
nat_lit
  1072901312360644737248441339698542216824993390630019808125341853972984585770385458286955751737646535791726054556999396601749581774956725065476992655795032337321868887725222403140808377853856561311501876538395191117997428708936113895847717096660953146670116184899497401676968661374610037846215935733

noncomputable def p22549 :=
nat_lit
  369204951733325859646627479118098170833544556685678735101762744603934696110410757550723398104894301733468921249580652498179366317291999573747800518021222757623743596565602781885551439800998971517258512108437305673694563267039726560155727502485927404632871594986559599

noncomputable def p22550 :=
nat_lit
  131523135322435906824766752893017318330910701072774602314738834070542611206232729414136080949605416809536673733360504216055614551429974176046179325716803069750619077568994197921379241481041556093483585245835277282155290819369192453815148149803215904891828203368214461406549772587304752365707261942801847

noncomputable def p22551 :=
nat_lit
  652889387237757652965818826006918680744055358539264141791360123814446537894391657035201788253902580252143127113395018416683761248430798466930884335444925090920981573234374163700981549327092574484014401254275546698512018730063425878288743819213320954871748424112331190235289661905923027926852540111109101568597089139553530100847093826604600834713758128945824457416294790389830103323842269811087421969715451991156440945652440100106048069038393292785181609294691325502083648378755874816

noncomputable def p22552 :=
@p22545 p22546 p22547 p22548
  p20578 p22549 p22498 p22550
  p20578 p22551 p22538 p22498

noncomputable def p22553 :=
nat_lit
  56204251203858225578150149791289448565856870412691733661019551880677245143253496951489419756575663437080091046035774470860723306633309865933499601651197272158649167894159278796245920010083498730019826716581483754217964144953102348031768998892843361448026382745932359110541243402695311832965307844839680926823561079855951076990476464780532828911351598615284371689425560138021

noncomputable def p22554 :=
nat_lit
  9417268426761892463105567719246562392350816513676086740176424983282011438804445546220191324664152398715383672875642978346991520067402495828436359717972840606536904084535992837334300937944301041511470946781327736565154689556704447231691584730866248686315404919058250828833882112000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p22555 :=
@Enclosure.Real.IsNear.subLit_tt_n
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p22484
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p22404 (Enclosure.sfrac false 1 16)))))

noncomputable def p22556 :=
@p22555
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p22486
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 4 1) Real.pi))
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p22404 (Enclosure.sfrac false 1 16)))))

noncomputable def p22557 :=
nat_lit
  39183778351958264850485003654239829034401242624291327407424394441656216630566502558687077459823967897276201511331847343106590811005258531180727587671527520624123261521095056169879640117046206714880331682361082059711375

noncomputable def p22558 :=
nat_lit
  326870361356666568617192429096807307763116853785012546707532231502590250105046156180255952766138293788904362926050412872069969750707502014290701472960551840441272172640591076207341407848881258019699981870326793457871524304485861963281264372554154860055536885782279779270400580787789105979119485893

noncomputable def p22559 :=
nat_lit
  28904010061066784803136311812762608396891147836282045964612903725445723774939408529572084464980646112179532191956070318005031515893955

noncomputable def p22560 :=
nat_lit
  11356855067118857664833184498250070849275646260739344691898284362197488876771842551971735167402555711886914400097909030211478150447104

noncomputable def p22561 :=
nat_lit
  2468929898038266713636643961459736479304989615883273487522242558388383392669519421021135175454462123109932938670207845994986046554032053482522658931042035582788343524487217796832222189687636988599899

noncomputable def p22562 :=
nat_lit
  594932197140979243429320605775993011376062085202953782707809604943507215782230251116795584150270640128000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p22563 :=
nat_lit
  405148374598788016508486209157876574417103570305631454123088496935498485086924269254045796322277339677717775571444003910658436354658945442085721533870479009244058178085444632510512199459278821098507893837931653541559606915276251021123441647088290177957251178906888418738329685627509732708847801277406290218826668083702564130128453148851265614622228480

noncomputable def p22564 :=
@p22556 p22557 p22547 p22558
  p20578 p22559 p22560 p22561
  p22562 p22563 p22546 p22547

noncomputable def p22565 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p22484
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p22404 (Enclosure.sfrac false 1 16)))))

noncomputable def p22566 :=
nat_lit
  11665583763783158180897362010339611633991621990731815556114458000086366359325242550732116643421416104396142455882554504651244770141670361156392599432517432020771126013915645834947847545837885002861655717440047902827442695512096057806535337800942988367431574517229196932592706248478820673121718905868149951590129246633

noncomputable def p22567 :=
nat_lit
  6415736122196620298810642787680057114558766074707948728239550710417561076066653048546415432802019904820496237552298536329609993870872147475354438227435583274203972055859200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p22568 :=
nat_lit
  8702676176688964253206593123757723871700512675657312596641888828942083587350052639485460092475825133433150302397608442927618578757385198406088587221619679331184029806838677440964717965704854078069159875

noncomputable def p22569 :=
@Enclosure.Real.IsNear.mulLit_ft p22484
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p22404 (Enclosure.sfrac false 1 16))))
  p22568

noncomputable def p22570 :=
nat_lit
  171431297963142706942819020873469362239979685423775290979727436720922285973614420078542380828894978226971976647459961143277961607704715958161726188516802462959136983188323298492011383261349291139133341334375481885299610846571709324158689634280658303268023637338235759815953416724210327938595301

noncomputable def p22571 :=
@p22569 p21002 p22570 p21004
  4502497571599429 4503599627370496 4290195057 119626865102028800000000
  p22557 p22547 p22566 p22567

noncomputable def p22572 :=
@Enclosure.Real.IsNear.mulLit_ff p22483
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p22573 :=
nat_lit
  423092391959918799283571683220726889081557482546488806878093059641288570714814918519113121303544506341913570549375003961826656763472025

noncomputable def p22574 :=
nat_lit
  62557736943081031387869646393716825305112555363080111654778694409775543625555882018083568758347117593677506730490397002523848787957763551333954239139838973759605712892189226979155904988688951

noncomputable def p22575 :=
nat_lit 20569209803974454071341510602306263112576869001108751481311777476795

noncomputable def p22576 :=
nat_lit 17121160916665483071190193476420586769614568899298924233782228895543558508241225990480101

noncomputable def p22577 :=
@p22572 p22573 p21008 p22574
  p21010 p22575 p21012 p22576
  p21014 p22568 p21002 p22570

noncomputable def p22578 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p22579 :=
@p22578
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p22580 :=
@p22579 p22575 p21012 p22576
  p21014 p22575 p21012 p22576
  p21014 p22573 p21008 p22574

noncomputable def p22581 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
        (Enclosure.sfrac false 12 1)))
    (Enclosure.sfrac false 1 1))
  p20538

noncomputable def p22582 :=
@p22581 p20539 1 p20541 4374903443936735
  9007199254740992 41 9007199254740992 p22575 p21012
  p22576 p21014

noncomputable def p22583 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
      (Enclosure.sfrac false 12 1)))
  (Enclosure.sfrac false 1 1) 13382102698677727 9007199254740992

noncomputable def p22584 :=
@p22583 41 9007199254740992 1 1 0 1
  4374903443936735 4374903443936735 9007199254740992 41
  9007199254740992

noncomputable def p22585 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 2 1)
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
    (Enclosure.sfrac false 12 1))
  2 1 0 1

noncomputable def p22586 :=
@p22585 13382102698677727 18014398509481984 41
  18014398509481984 13382102698677727 9007199254740992 41
  9007199254740992 (Enclosure.Real.IsNear.const false 2 1)
  (@p22507 1 13382102698677727 13382102698677727
    18014398509481984 41 18014398509481984
    (p22512 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p22587 :=
@p22580 p21010
  (p22582 d263
    (p22584 (p22586 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (p22582 d263
    (p22584 (p22586 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))

noncomputable def p22588 :=
@p22577 p21004 (p22587 (Eq.refl true))
  (p22582 d263
    (p22584 (p22586 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p22589 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p22404 (Enclosure.sfrac false 1 16))))
  true

noncomputable def p22590 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p22404 (Enclosure.sfrac false 1 16)))
  (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
    (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 28695485137915723))
    (@Nat.cast Real Real.instNatCast 18014398509481984))
  true

noncomputable def p22591 :=
nat_lit 386814374453110863614106191600257321411327969360000033896951991107230871817926481435

noncomputable def p22592 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p22404 (Enclosure.sfrac false 1 16)))
  true p22591

noncomputable def p22593 :=
nat_lit 766661683112590153470302165769119897512074181539840096130567552971740513498133715333097428623691435648419

noncomputable def p22594 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (p22404 (Enclosure.sfrac false 1 16)) p20538
  p20539 1

noncomputable def p22595 :=
nat_lit 82272267874488847516501573969855

noncomputable def p22596 :=
nat_lit 61989858270837177092554322683839

noncomputable def p22597 :=
@p22445 (Enclosure.sfrac false 1 16) p22596
  p21036 1835922760180336639 p21036 1 16 0

noncomputable def p22598 :=
nat_lit 1316356285991821560264025183517680

noncomputable def p22599 :=
nat_lit 179080672637957703834874205886529

noncomputable def p22600 :=
@Enclosure.Real.IsNear.subLit_ff_n
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
      (Enclosure.sfrac false 12 1))
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
      (Enclosure.sfrac false 12 1)))
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
    (Enclosure.sfrac false 12 1))
  p22599

noncomputable def p22601 :=
nat_lit 1116710010437168681046690731521031862660498456576

noncomputable def p22602 :=
@p22600 p21036 1097332421291575295 p21036
  13382102698677727 18014398509481984 41 18014398509481984
  p22601 p22596 p21036 1835922760180336639

noncomputable def p22603 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
    (Enclosure.sfrac false 12 1))
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
    (Enclosure.sfrac false 12 1))
  13382102698677727 18014398509481984 41

noncomputable def p22604 :=
@p22603 18014398509481984 13382102698677727 18014398509481984
  41 18014398509481984 p22599 p21036
  1097332421291575295 p21036
  (@p22507 1 13382102698677727 13382102698677727
    18014398509481984 41 18014398509481984
    (p22512 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p22605 :=
p22604
  (@p22507 1 13382102698677727 13382102698677727
    18014398509481984 41 18014398509481984
    (p22512 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p22606 :=
@p22602 p21036 (p22605 (Eq.refl true))
  (@p22507 1 13382102698677727 13382102698677727
    18014398509481984 41 18014398509481984
    (p22512 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p22607 :=
@p22594 p20541 p22595 p21036
  1835922760180336639 p21036 p22591 p15946
  p22593 p21033 d263
  (@p22597 1 p22598 p22595 p21036
    1835922760180336639 p21036
    (p22606 (Eq.refl true) (Eq.refl true))
    (Enclosure.Real.IsNear.const false 1 16) (Eq.refl true)
    (Eq.refl true))

noncomputable def p22608 :=
@p22590 28695485137915723 18014398509481984 641
  18014398509481984 true 9004995143198858 9007199254740992 1
  3565158400000000
  (@p22592 p15946 p22593 p21033
    28695485137915723 18014398509481984 641 18014398509481984
    (p22607 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_true_div 28695485137915723 18014398509481984)

noncomputable def p22609 :=
nat_lit
  35584201053317625997561131821588967167623687248002782458513104584320593634788385818096138497253483100578169254486866675416519234677570850063671457714487543252058717697242447685895893160299324580752070740479034403375107700570151752742978539721008974051895950353048366792832093039088700957977278865637553641680389508530541391986674699650249587441

noncomputable def p22610 :=
nat_lit
  661818996425439523095547487862194753598477959590497486592419699595387533442452708515670474714376155634513799462025596307709543262908447113869605452677305601528762496048745267225256619334456582503054322195677125163477930158384694162405392905297912595353093294093989640223687030380090575255797110570082168108575469955981939359582432320227901440000

noncomputable def p22611 :=
nat_lit
  143308328377411997714996026280069302119576868370075886398873101936785552045933561793277726519061778300867424102528765172455592162214357717943523642072903556535590830219696980546769583073445933111298944804965832134341235152264073836231624459950556750394532977749950625119580609728235225543607805519579402616067167611516387908713201

noncomputable def p22612 :=
nat_lit
  428141578702700561602653947559334103595167571801680281047028519429890879147460609820975025995982917907499678780156100170176910497429648451152209953294842081745271628389350037165760198854327606814370627339486670079744369447349416233618596259816013073760329077055066943073088724302143155767455596537603839906255702009027145923046926676008321743601

noncomputable def p22613 :=
nat_lit
  55813402031878733114391171476378424220138307925465288035960727999211015320313511751488210034245722458510663754630825288616838148505279039936336726509119439062258970500110850869329974897205838457757581171835437555453305443357109207696188135013457295541444201135259792992197606228720971846572222991410262843823197966287810219324785125672553021440000

noncomputable def p22614 :=
BSN.sin_dyadic_bound_f 28695485137915723 18014398509481984 6 5
  9007199254740992 3565158400000000 p22609 p22610
  p22611 p22612 p22613

noncomputable def p22615 :=
@BSN.binarySplit_of_base5 (BSN.sinEvenP 28695485137915723) (BSN.sinEvenQ 18014398509481984)
  0 5 p22609 p22610 p22611
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p22616 :=
p22614 p22611 9004995143198858 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p22615 (Eq.refl true))

noncomputable def p22617 :=
@BSN.binarySplit_of_base5 (BSN.sinOddP 28695485137915723) (BSN.sinOddQ 18014398509481984)
  0 5 p22612 p22613 p22611
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p22618 :=
p22608
  (BSN.sin_neg_of_bound 28695485137915723 18014398509481984 false 9004995143198858
    9007199254740992 1 3565158400000000
    (p22616 (p22617 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p22619 :=
p22571 p22588
  (@p22589 9004995143198858 9007199254740992 2303280932909481984
    p21028 4502497571599429 4503599627370496 4290195057
    119626865102028800000000 (p22618 (Eq.refl true))
    (Eq.refl true))

noncomputable def p22620 :=
@p22565 true p22557 p22547 p22566
  p22567 p22557 p22547 p22558
  p20578 (p22619 (Eq.refl true)) (Eq.refl true)

noncomputable def p22621 :=
nat_lit
  290126900432253580087597830972020543642680980580064347786020977583556545640477559398516447968029865873866843017035325845

noncomputable def p22622 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p22486
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 4 1) Real.pi))
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p22404 (Enclosure.sfrac false 1 16))))
  p22621

noncomputable def p22623 :=
nat_lit
  21448840326903925211259895611218148854195455371683038293290507520355098396883642359516350189222226220936132772618901172537125839851043370133898425818643364564860359566648768403

noncomputable def p22624 :=
@p22622 p20387 p22623 p21065
  99625405358839 4503599627370496 4290195057 119626865102028800000000
  p22559 p22560 p22561 p22562

noncomputable def p22625 :=
nat_lit 61707629411923362214024531806918789337730607003326254443935332430385

noncomputable def p22626 :=
nat_lit 51363482749996449213570580429261760308843706697896772701346686686630675524723677971440303

noncomputable def p22627 :=
@Enclosure.Real.IsNear.mulLit_ff p22486
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 4 1) Real.pi)
  p22625 p21012 p22626 p21014

noncomputable def p22628 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 3 1)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p22629 :=
@p22628 3 1 0 1 p22575
  p21012 p22576 p21014 p22625
  p21012 p22626

noncomputable def p22630 :=
@p22629 p21014 (Enclosure.Real.IsNear.const false 3 1)
  (p22582 d263
    (p22584 (p22586 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p22631 :=
@p22627 p20538 p2930 1 p20548
  p22621 p20387 p22623 p21065
  p22630 d265 (Eq.refl true)

noncomputable def p22632 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p22404 (Enclosure.sfrac false 1 16)))
  (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
    (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 28695485137915723))
    (@Nat.cast Real Real.instNatCast 18014398509481984))
  true

noncomputable def p22633 :=
@p22632 28695485137915723 18014398509481984 641
  18014398509481984 true 199250810717678 9007199254740992 1
  3565158400000000
  (@p22592 p15946 p22593 p21033
    28695485137915723 18014398509481984 641 18014398509481984
    (p22607 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_true_div 28695485137915723 18014398509481984)

noncomputable def p22634 :=
nat_lit
  8486839790471073772858990945820149411929395613289148739876659874696626197377428619806328540540421207672286020525888395124974421606583875188786177188462258647022504501820884445570664033282260406106673217201213263195490907268876579335304053722628503547443470707774682919248029095904856975755977054069038798084122327482585022122747608180021066481

noncomputable def p22635 :=
nat_lit
  31515190305973310623597499422009273980879902837642737456781890456923215878212033738841451176875055030214942831525028395605216345852783195898552640603681219120417261716606917486916981873069361071574015342651291674451330007542128293447875852633233933112052061623523316201127953827623360726466529074765817528979784283618187588551544396201328640000

noncomputable def p22636 :=
nat_lit
  130364463185541996875438422746383017874263650515264311355935797955322075111240957374686109472378082271674763702045340682249754098297509139648686828221093051159793603501548597719173082328881743508976922806083455044943208474047266342662413830097583000831235928216353468796248964686517443404841117130054288671087498553565490436858310251882546526961

noncomputable def p22637 :=
nat_lit
  7280008960679834754051022366484142289583257555495472352516616695549262867866979793672375221858137711979651794082281559384804975891992918252565659979450361616816387456536197939477822812679022407533597544152448376798257231742231635786459321958277038548884026235033886042460557334180996327813768216270903849194330169515801332955406755522506915840000

noncomputable def p22638 :=
BSN.cos_dyadic_bound_t 28695485137915723 18014398509481984 6 5
  9007199254740992 3565158400000000 p22634 p22635
  p22611 p22636 p22637

noncomputable def p22639 :=
@BSN.binarySplit_of_base5 (BSN.cosEvenP 28695485137915723) (BSN.cosEvenQ 18014398509481984)
  0 5 p22634 p22635 p22611
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p22640 :=
p22638 p22611 199250810717678 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p22639 (Eq.refl true))

noncomputable def p22641 :=
@BSN.binarySplit_of_base5 (BSN.cosOddP 28695485137915723) (BSN.cosOddQ 18014398509481984)
  0 5 p22636 p22637 p22611
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p22642 :=
p22633
  (BSN.cos_neg_of_bound 28695485137915723 18014398509481984 true 199250810717678
    9007199254740992 1 3565158400000000
    (p22640 (p22641 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p22643 :=
p22624 p22631
  (@p22439 199250810717678 9007199254740992 2303280932909481984
    p21028 99625405358839 4503599627370496 4290195057
    119626865102028800000000 (p22642 (Eq.refl true))
    (Eq.refl true))

noncomputable def p22644 :=
@Enclosure.Real.IsNear.recentre' p22487 true p22546 p22547
  p22553 p22554 p22546 p22547
  p22548 p20578
  (@p22564 p22553 p22554 p22620
    (p22643 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p22645 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 3 1) p22488)
    (@iteratedDeriv Real (@DenselyNormedField.toNontriviallyNormedField Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal Real Real.instRCLike))
      (@OfNat.ofNat Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
        (Enclosure.sfrac false 12 1))))

noncomputable def p22646 :=
nat_lit
  817791312224884184652123799284289727462793478773120982378933489100045068081281165843643172918817795895636632809271269206739573124811525833451778870328043950329796477346093256920724476853206695036818192533515528346936815002045016774820268663872006503742712212095504248472765047848093927548834274952204214018447558431391530436668366559768413427721292608626320259876950364583214724007628697

noncomputable def p22647 :=
nat_lit
  1117778879079029370288710350112027341429447208099924445143384691902105582788129674699154138958987545885733880881937871264016629353164058320914660638763524680615485030114794477115728548550418577420149815993853542400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p22648 :=
nat_lit 126917785405424888309355323025654606143696158668533260687508853587019

noncomputable def p22649 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 3 1) p22488)
  (@iteratedDeriv Real (@DenselyNormedField.toNontriviallyNormedField Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal Real Real.instRCLike))
    (@OfNat.ofNat Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
      (Enclosure.sfrac false 12 1)))
  p22648

noncomputable def p22650 :=
nat_lit 1094189809993722961702023518527869753837602414001393883744154311129457789344718898394492120675623

noncomputable def p22651 :=
nat_lit
  2909008777248525894457656743870219693046468282967993781121441754982303602194418277321933684163946277048065556245549143244403531793528109812256492873296861801826463466666444604407909221572776134243821

noncomputable def p22652 :=
nat_lit
  598008216632976371697735644702348584536405246902083247220875921706093794716375762404103004004990504111786204800430166155026589905240121409306972824498630058082565445957748647537262486126146850127872

noncomputable def p22653 :=
nat_lit
  10924713071037658933862974601358757261893345019299856759684552679605803118726288023391801852009464073422686577628613019320007238336959454764252607105806421985320597393790282592920523402492771713647578484096454611153089087242763629351483904283006378930722316992944043247363985339

noncomputable def p22654 :=
nat_lit
  281182112158949773925658656730373866179356069893869789568797223288239848791967991894940042881493178571870056914595055945200516628468393730563032198804072740945920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p22655 :=
@p22649 p21012 p22650 p21094
  p22651 p22652 p22653 p22654
  p22549 p22498 p22646 p22647

noncomputable def p22656 :=
nat_lit 42305928468474962769785107675218202047898719556177753562502951195673

noncomputable def p22657 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 3 1) p22488
  3 1 0 1 p22656 p21012

noncomputable def p22658 :=
nat_lit 364729936664574320567341172842623251279200804667131294581384770376485929781572966131497373558541

noncomputable def p22659 :=
@Enclosure.Real.IsNear.neg
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
          (Enclosure.sfrac false 12 1)))))

noncomputable def p22660 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
        (Enclosure.sfrac false 12 1))))
  p20538

noncomputable def p22661 :=
@p22660 p20539 1 p20541 8998126516260709
  9007199254740992 873417841 59813432551014400000000 p22656
  p21012 p22658 p21094

noncomputable def p22662 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
        (Enclosure.sfrac false 12 1))))
  true

noncomputable def p22663 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
      (Enclosure.sfrac false 12 1)))
  (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
    (@Nat.cast Real Real.instNatCast 84082231055500187)
    (@Nat.cast Real Real.instNatCast 18014398509481984))
  false

noncomputable def p22664 :=
@p22663 84082231055500187 18014398509481984 129
  9007199254740992 true 17996253032521418 18014398509481984 1
  3565158400000000
  (@p22504 p16711 p22505 p20932
    84082231055500187 18014398509481984 129 9007199254740992
    (p22513 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div 84082231055500187 18014398509481984)

noncomputable def p22665 :=
BSN.sin_reduce2
  (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
    (@Nat.cast Real Real.instNatCast 84082231055500187)
    (@Nat.cast Real Real.instNatCast 18014398509481984))
  (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
    (@Nat.cast Real Real.instNatCast p22515)
    (@Nat.cast Real Real.instNatCast p14600))
  p2138 p2102 false

noncomputable def p22666 :=
nat_lit
  50471879917635063901912135347964060104813788273340727153862194404985940320205143608872759101846936051718241983563030200571976077186308779312768409760129420927378179301964169204767884384276797544600608436148767086637685383445903353888442930335459264472425921747234284729887890113423977480177176987877552848251828305243503697114194904310338670458253579579516248820233677804715415555169905242708262792690605996641

noncomputable def p22667 :=
nat_lit
  607393007004041533761713106562857849101995450081609106639213598646430145992879284294642346282092857513171690328050476824298836203347506071983103389443773142583491145652077837465403483105444109114352342181410536848296624049648519325358519151800125214110689369978250416676639666141180331013720644975067462827198480017216783836316625387219534721323983243445275684015125961984250465048065683449814928400154734344801

noncomputable def p22668 :=
BSN.sin_dyadic_bound_f 56296097872430417497 36893488147419103232 6 5
  18014398509481984 7137280000000001 p22666 p21110
  p22519 p22667 p21112

noncomputable def p22669 :=
@BSN.binarySplit_of_base5 (BSN.sinEvenP 56296097872430417497) (BSN.sinEvenQ 36893488147419103232)
  0 5 p22666 p21110 p22519
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p22670 :=
p22668 p22519 17996253032521418 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p22669 (Eq.refl true))

noncomputable def p22671 :=
@BSN.binarySplit_of_base5 (BSN.sinOddP 56296097872430417497) (BSN.sinOddQ 36893488147419103232)
  0 5 p22667 p21112 p22519
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p22672 :=
@BSN.sin_arg_round false 17996253032521418 18014398509481984 p22515
  p14600 56296097872430417497 36893488147419103232 7137280000000001
  7130316800000000
  (p22670 (p22671 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p22673 :=
p22665 17996253032521418 18014398509481984 0 p2139
  7130316800000000 3565158400000000 p22517 d102
  p22672 (Eq.refl true) (Eq.refl true)

noncomputable def p22674 :=
p22661 d263
  (@p22662 17996253032521418 18014398509481984 468912632854740992
    p20927 8998126516260709 9007199254740992 873417841
    59813432551014400000000
    (p22664 (p22673 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p22675 :=
@Neg.neg Real Real.instNeg
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p22483
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p22404 (Enclosure.sfrac false 1 16)))))

noncomputable def p22676 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22675
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 4 1) Real.pi)
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p22404 (Enclosure.sfrac false 1 16)))))

noncomputable def p22677 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22676
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) p22488)
    (@iteratedDeriv Real (@DenselyNormedField.toNontriviallyNormedField Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal Real Real.instRCLike))
      (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
        (Enclosure.sfrac false 12 1))))

noncomputable def p22678 :=
@Enclosure.Real.IsNear.of_eq
  (@iteratedDeriv Real (@DenselyNormedField.toNontriviallyNormedField Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal Real Real.instRCLike))
    (@OfNat.ofNat Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
      (Enclosure.sfrac false 12 1)))
  (p22403
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22677
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p22490
        (Zeta.RiemannSiegel.correction
          (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
            (Enclosure.sfrac false 12 1))))))

noncomputable def p22679 :=
@p22407
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22677
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p22490
      (Zeta.RiemannSiegel.correction
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
          (Enclosure.sfrac false 12 1)))))
  401457751629956851

noncomputable def p22680 :=
nat_lit
  7246114355589528804550551396831194485481580915660168307450278975659697798726345688178413433351907121099773638180571796516035266388152915232740240919672485115596238150352880923117471

noncomputable def p22681 :=
nat_lit
  33196124551047943668099262909529289208099569857939495199965258637525222491303265171197656391576830354305583092890406313459161208603294202463094998672911709496489454427212076189483008

noncomputable def p22682 :=
nat_lit
  462595514733267237709748147349209132697283810098039111642820731783284685219263120282076645999812454630301743144483643576778825539557874269602175469174009419358772266267821997481705824586100491675101712865262660451297605663113350357940698870234980942136759427477

noncomputable def p22683 :=
nat_lit
  265348626776859339667435764532419135988630842126522547823028341568156597799680077710226018760396817548585289145319562946113077932739504251034664960000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p22684 :=
@p22679 18014398509481984 130643 18014398509481984
  p22680 p22681 p22682 p22683
  p22651 p22652 p22653 p22654

noncomputable def p22685 :=
nat_lit
  21744502017904797597005369608282416425966528549258007203963780992471974167489222008901229253504392379395345030433111820872463770008599563957423536596699043380131181211342731511003233

noncomputable def p22686 :=
@Enclosure.Real.IsNear.subLit_ff_n p22677
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p22490
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
        (Enclosure.sfrac false 12 1))))
  p22685 p22681

noncomputable def p22687 :=
nat_lit
  27180529873614462571805345401332993748004626451917421125200130617585147134827376626530420643136858716543198554063497386920390218638462681233141072520037977348383798253269488120844382110219888350921619156643487154189159701247503343941967864553535360223197613381

noncomputable def p22688 :=
nat_lit
  15608742751579961156907986148965831528742990713324855754295784798126858694098828100601530515317459855799134655607033114477239878396441426531450880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p22689 :=
nat_lit
  714673871103431900068799917924747868322419456554205341076798803286248196677660159740661901532007560336817128628506183999284887344451558172759206532397

noncomputable def p22690 :=
nat_lit
  66454511263792219178275831147619493795947700975179516410625845830115171092518581902625037274333198581832609675829913924169823714498901648803978348694270511344262670269788494655505561623809978742520814679668705340245342659

noncomputable def p22691 :=
nat_lit
  33491705266935307330437184085122071734317778379895629667756049393608863505772629019702126316652178294685633791760793600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p22692 :=
nat_lit
  5929840668832042001329783286478774278729755567381183563845555363281203550772829177848115284975944975074006630910868629846342535503438095485747765100365013018455404182216220323388210826056615084650021054844033239691899576474365925837716247781021247678432090845932460041562043018392796407254303462592308616732891984934380834624897024

noncomputable def p22693 :=
@p22686 p22687 p22688 p22689
  p17975 p22690 p22691 p22692
  p22680 p22681 p22682 p22683

noncomputable def p22694 :=
@Enclosure.Real.IsNear.subLit_ff_p p22676
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) p22488)
    (@iteratedDeriv Real (@DenselyNormedField.toNontriviallyNormedField Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal Real Real.instRCLike))
      (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
        (Enclosure.sfrac false 12 1))))

noncomputable def p22695 :=
nat_lit
  2612436605445324823383896880694121267274824130338907407247177762805958206471942852648805498355490060487957877615917760508998910075109330831863714659743

noncomputable def p22696 :=
nat_lit
  204586912993508866875824356051724947013540127877691549342705710506008362275292159680204380770369009821930417757972504438076078534117837065833032974336

noncomputable def p22697 :=
nat_lit
  8451117586465925887662225927643719098219613740438238673351845222669194762644732894140702870590117705077572983162385634198207099297768511375995987629413014491938876655350451521650087500017652396757278891112013010833

noncomputable def p22698 :=
nat_lit
  10717345685419298345739898907239062954981689081566601493681935805954836321847241286304680421328697054299402813363453952000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p22699 :=
nat_lit
  402147572343818610078688245701497842741849355533008370657665705308215892986449820312440696238413709873114225651411383865921494215602272409870784145850185135059701816090876697401427871

noncomputable def p22700 :=
nat_lit
  461859768314705963792179388727720038824690215437469412439912988279861443661990958460824339125911393407319746436189403757883258098907762589258811720394600615434476201519748782231212485257466678481986277341483163565236210873616901732939751203038261123794359427477

noncomputable def p22701 :=
nat_lit
  4448640542424266810944020649634381995341613852780216951315627361869180761158074250790832353823584047187899938647420386605090956442173296877407637469202583288979295185334996732625293626892156624035228200285640197568217068956742218894172214056725530920576138936454035892564228536168244714011458805085125996581893233136839697302028288

noncomputable def p22702 :=
@p22694 p22695 p22696 p22697
  p22698 p22699 p22681 p22700
  p22683 p22701 p22685 p22681

noncomputable def p22703 :=
@Enclosure.Real.IsNear.subLit_ft p22675
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 4 1) Real.pi)
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p22404 (Enclosure.sfrac false 1 16)))))

noncomputable def p22704 :=
nat_lit
  42150751053247704984244840803514199954382658380611384192696303665780564007954925184242115497159782715280815052203481008940762266514805383142662978975

noncomputable def p22705 :=
nat_lit
  3621136620667184214081951161942375674058335444357227346138459420664282365099845650907194017642646328124297305741513755029657372704288080774942024009356631416868105455350451521650087500017652396757278891112013010833

noncomputable def p22706 :=
nat_lit 21169111131005205856048570560490701389249572074207602566048607803513

noncomputable def p22707 :=
nat_lit 1791539510604386448647252369741786521795350263204544571423676972813378843868189050044584679538957

noncomputable def p22708 :=
nat_lit
  4401946972132375996046620750594574363524788262882316475509674683180868237027732583338913884107023838314368711100506776361752438705096923228032312767084084494606718490444208064116377134642418346060983525126655304531968

noncomputable def p22709 :=
@p22703 p22704 p22696 p22705
  p22698 p22706 p21092 p22707
  p21094 p22708 p22695 p22696

noncomputable def p22710 :=
@Enclosure.Real.IsNear.neg
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p22483
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p22404 (Enclosure.sfrac false 1 16)))))

noncomputable def p22711 :=
@Enclosure.Real.IsNear.mulLit_ft p22483
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p22404 (Enclosure.sfrac false 1 16))))
  p22573

noncomputable def p22712 :=
@p22711 p21008 p22574 p21010
  99625405358839 4503599627370496 4290195057 119626865102028800000000
  p22704 p22696 p22705 p22698

noncomputable def p22713 :=
p22712 (p22587 (Eq.refl true))
  (@p22439 199250810717678 9007199254740992 2303280932909481984
    p21028 99625405358839 4503599627370496 4290195057
    119626865102028800000000 (p22642 (Eq.refl true))
    (Eq.refl true))

noncomputable def p22714 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 4 1) Real.pi)
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p22404 (Enclosure.sfrac false 1 16))))
  p20538

noncomputable def p22715 :=
@p22714 p2930 1 p20548 4502497571599429
  4503599627370496 4290195057 119626865102028800000000 p22706
  p21092 p22707 p21094

noncomputable def p22716 :=
p22715 d265
  (@p22589 9004995143198858 9007199254740992 2303280932909481984
    p21028 4502497571599429 4503599627370496 4290195057
    119626865102028800000000 (p22618 (Eq.refl true))
    (Eq.refl true))

noncomputable def p22717 :=
@p22702 p22687 p22688
  (@p22709 p22697 p22698
    (@p22710 true p22704 p22696 p22705
      p22698 (p22713 (Eq.refl true)))
    (p22716 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p22718 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1) p22488)
  (@iteratedDeriv Real (@DenselyNormedField.toNontriviallyNormedField Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal Real Real.instRCLike))
    (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
      (Enclosure.sfrac false 12 1)))
  p22656

noncomputable def p22719 :=
nat_lit
  9505702555221929168423957322417872361334093396643993365134612886997044499136420761557017464858232182982235146743927

noncomputable def p22720 :=
nat_lit
  9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704

noncomputable def p22721 :=
nat_lit
  18507831845295005597435998976447243748613715967794324459453708819495245511754160394410470886248749461045189713123636581624870149831957620455543734407847

noncomputable def p22722 :=
nat_lit
  133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p22723 :=
@p22718 p21153 p22658 p21166
  p22719 p22720 p22721 p22722
  p22699 p22681 p22700 p22683

noncomputable def p22724 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 2 1) p22488
  2 1 0 1 p22656 p21012

noncomputable def p22725 :=
@Neg.neg Real Real.instNeg
  (p22482
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p22404 (Enclosure.sfrac false 1 16)))))

noncomputable def p22726 :=
@Enclosure.Real.IsNear.of_eq
  (@iteratedDeriv Real (@DenselyNormedField.toNontriviallyNormedField Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal Real Real.instRCLike))
    (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
      (Enclosure.sfrac false 12 1)))
  (p22403
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22725
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p22488
        (Zeta.RiemannSiegel.correction
          (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
            (Enclosure.sfrac false 12 1))))))

noncomputable def p22727 :=
@p22407
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22725
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p22488
      (Zeta.RiemannSiegel.correction
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
          (Enclosure.sfrac false 12 1)))))
  401457751629956851

noncomputable def p22728 :=
nat_lit 23677964908207322062044752153930473429490679038011336501751293978759033498152883169160963259226477

noncomputable def p22729 :=
nat_lit 546812681195752981093125556779405341338292357723303109106442651602488249799843980805878294255763456

noncomputable def p22730 :=
nat_lit
  195487851236136035391656899584378779611514383625124637956505476288895384956970628489429425774484482446631566065880846493062075678148999

noncomputable def p22731 :=
nat_lit
  31495448272550005155211307922363110936089435829054233418732462850152371262062592000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p22732 :=
@p22727 18014398509481984 130643 18014398509481984
  p22728 p22729 p22730 p22731
  p22719 p22720 p22721 p22722

noncomputable def p22733 :=
nat_lit 92612817192114146465852815227884867021294093219586189859914547774653233826082750055

noncomputable def p22734 :=
@Enclosure.Real.IsNear.subLit_ff_n p22725
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p22488
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
        (Enclosure.sfrac false 12 1))))
  p22733 p16541

noncomputable def p22735 :=
nat_lit 2471365497103546489617957631248679008547767831392115982071488204655243352528151116750810568882104044693912761283

noncomputable def p22736 :=
nat_lit
  17903089583654721738646064706223973494212166218093348913232866181120000000000000000000000000000000000000000000000000000000000

noncomputable def p22737 :=
nat_lit 1692042160892755864795835270978789720416351122929823216937535872411322570321384805323003299456735597

noncomputable def p22738 :=
nat_lit
  191140179075256413289221169537187041659293458783292198027576825363616552253880019146641592256470103581324050104541950108747502878148999

noncomputable def p22739 :=
nat_lit
  718725716537293829321138982214800650366234517708499626610738041523771875703668672605438982525043895911930180810914205860052907970410489023786951179851126282984551081020695634771968

noncomputable def p22740 :=
@p22734 p22735 p22736 p22737
  p22729 p22738 p22731 p22739
  p22728 p22729 p22730 p22731

noncomputable def p22741 :=
@Enclosure.Real.IsNear.neg
  (p22482
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p22404 (Enclosure.sfrac false 1 16)))))

noncomputable def p22742 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p22743 :=
@p22742
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p22404 (Enclosure.sfrac false 1 16))))
  p22575

noncomputable def p22744 :=
@p22743 p21012 p22576 p21014
  4502497571599429 4503599627370496 4290195057 119626865102028800000000
  p22733 p16541 p22735 p22736

noncomputable def p22745 :=
p22744
  (p22582 d263
    (p22584 (p22586 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (@p22589 9004995143198858 9007199254740992 2303280932909481984
    p21028 4502497571599429 4503599627370496 4290195057
    119626865102028800000000 (p22618 (Eq.refl true))
    (Eq.refl true))

noncomputable def p22746 :=
@Enclosure.Real.IsNear.mulLit_ff p22488
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
      (Enclosure.sfrac false 12 1)))
  p22656 p21012 p22658

noncomputable def p22747 :=
nat_lit 39995391240582559550541741455989

noncomputable def p22748 :=
nat_lit 81129638414606681695789005144064

noncomputable def p22749 :=
nat_lit 60825076773766640488062637

noncomputable def p22750 :=
nat_lit 63382530011411470074835160268800000000

noncomputable def p22751 :=
@p22407
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p22404 (Enclosure.sfrac false 1 16))))
  401457751629956851

noncomputable def p22752 :=
@p22751 18014398509481984 130643 18014398509481984
  99625405358839 4503599627370496 4290195057 119626865102028800000000
  p22747 p22748 p22749 p22750

noncomputable def p22753 :=
p22752
  (p22501
    (@Enclosure.Real.IsNear.neg p22411 false 401457751629956851
      18014398509481984 130643 18014398509481984
      (p22529 (Eq.refl true))))
  (@p22439 199250810717678 9007199254740992 2303280932909481984
    p21028 99625405358839 4503599627370496 4290195057
    119626865102028800000000 (p22642 (Eq.refl true))
    (Eq.refl true))

noncomputable def p22754 :=
@p22746 p21094 p22747 p22748
  p22749 p22750 p22737 p22729
  p22738 p22731
  (@p22659 true p22656 p21012 p22658
    p21094 (p22674 (Eq.refl true)))
  (@p22405 false p22747 p22748 p22749
    p22750
    (BSN.correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
        (Enclosure.sfrac false 12 1))
      (p22406 (Eq.refl true) (Eq.refl true)
        (p22173 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p22753 (Eq.refl true)))

noncomputable def p22755 :=
p22732
  (p22501
    (@Enclosure.Real.IsNear.neg p22411 false 401457751629956851
      18014398509481984 130643 18014398509481984
      (p22529 (Eq.refl true))))
  (p22740
    (@p22741 true p22733 p16541 p22735
      p22736 (p22745 (Eq.refl true)))
    (p22754 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p22756 :=
p22723
  (@p22724 p22658 p21094 p22656
    p21153 p22658 p21166
    (Enclosure.Real.IsNear.const false 2 1)
    (@p22659 true p22656 p21012 p22658
      p21094 (p22674 (Eq.refl true)))
    (Eq.refl true))
  (@p22726 false p22719 p22720 p22721
    p22722
    (BSN.deriv_correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
        (Enclosure.sfrac false 12 1))
      (p22406 (Eq.refl true) (Eq.refl true)
        (p22173 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p22755 (Eq.refl true)))

noncomputable def p22757 :=
nat_lit
  17868905614761582175866511421339857754812618106755515752592375885066534308715489114453286400628794164785509795263686873

noncomputable def p22758 :=
nat_lit
  152307315530716752621496641582402690568199569531835255573516669331325214425312064752558824510745240539069412236818730333931997976771422837982748978622055598709137327875436721072589241

noncomputable def p22759 :=
@Enclosure.Real.IsNear.mulLit_ff p22490
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
      (Enclosure.sfrac false 12 1)))
  p22757 p21205 p22758

noncomputable def p22760 :=
@Enclosure.Real.IsNear.neg
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 4 1)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) Real.pi Real.pi))
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
          (Enclosure.sfrac false 12 1)))))

noncomputable def p22761 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 4 1)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) Real.pi Real.pi))
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
        (Enclosure.sfrac false 12 1))))
  p20550

noncomputable def p22762 :=
@p22761 p20555 p20551 p20557
  808350448685697 18014398509481984 873417841 59813432551014400000000
  p22757 p21205 p22758 p21208

noncomputable def p22763 :=
p22762 d267
  (@p22415 808350448685697 18014398509481984 468912632854740992
    p20927 808350448685697 18014398509481984 873417841
    59813432551014400000000
    (p22514 (p22526 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p22764 :=
@p22759 p21208 p22747 p22748
  p22749 p22750 p22689 p17975
  p22690 p22691
  (@p22760 true p22757 p21205 p22758
    p21208 (p22763 (Eq.refl true)))
  (@p22405 false p22747 p22748 p22749
    p22750
    (BSN.correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
        (Enclosure.sfrac false 12 1))
      (p22406 (Eq.refl true) (Eq.refl true)
        (p22173 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p22753 (Eq.refl true)))

noncomputable def p22765 :=
p22684
  (p22501
    (@Enclosure.Real.IsNear.neg p22411 false 401457751629956851
      18014398509481984 130643 18014398509481984
      (p22529 (Eq.refl true))))
  (p22693
    (p22717 (p22756 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true))
    (p22764 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p22766 :=
p22655
  (@p22657 p22658 p21094 p22648
    p21012 p22650 p21094
    (Enclosure.Real.IsNear.const false 3 1)
    (@p22659 true p22656 p21012 p22658
      p21094 (p22674 (Eq.refl true)))
    (Eq.refl true))
  (@p22678 false p22651 p22652 p22653
    p22654
    (BSN.iteratedDeriv_two_correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
        (Enclosure.sfrac false 12 1))
      (p22406 (Eq.refl true) (Eq.refl true)
        (p22173 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p22765 (Eq.refl true)))

noncomputable def p22767 :=
@p22645 false p22549 p22498 p22646
  p22647 p22549 p22498 p22550
  p20578 (p22766 (Eq.refl true)) (Eq.refl true)

noncomputable def p22768 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 3 1) p22490)
    (@iteratedDeriv Real (@DenselyNormedField.toNontriviallyNormedField Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal Real Real.instRCLike))
      (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
        (Enclosure.sfrac false 12 1))))

noncomputable def p22769 :=
nat_lit
  52091488031947443665135979075282324177483894724002217172823114729569223710300830792934503162795801769721624679134655726034487470489788214580686496085519052189380769464076684901114258074190356084491882620965773606028459512823929268036686157149660685674401848196461396770233371278500914921650968101825051996518516965119820963355188100581841523029137

noncomputable def p22770 :=
nat_lit
  70541764670976880294710933682749739567211585948121427299926174604741097794019438488795019832100764502899364072392113416100717568282000180234076872179937382680040090657825661902651392000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p22771 :=
nat_lit
  53606716844284746527599534264019573264437854320266547257777127655199602926146467343359859201886382494356529385791060619

noncomputable def p22772 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 3 1) p22490)
  (@iteratedDeriv Real (@DenselyNormedField.toNontriviallyNormedField Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal Real Real.instRCLike))
    (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
      (Enclosure.sfrac false 12 1)))
  p22771

noncomputable def p22773 :=
nat_lit
  456921946592150257864489924747208071704598708595505766720550007993975643275936194257676473532235721617208236710456191001795993930314268513948246935866166796127411983626310163217767723

noncomputable def p22774 :=
@p22772 p21205 p22773 p21208
  p22719 p22720 p22721 p22722
  p22540 p22541 p22769 p22770

noncomputable def p22775 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 3 1) p22490
  3 1 0 1 p22757 p21205

noncomputable def p22776 :=
p22774
  (@p22775 p22758 p21208 p22771
    p21205 p22773 p21208
    (Enclosure.Real.IsNear.const false 3 1)
    (@p22760 true p22757 p21205 p22758
      p21208 (p22763 (Eq.refl true)))
    (Eq.refl true))
  (@p22726 false p22719 p22720 p22721
    p22722
    (BSN.deriv_correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
        (Enclosure.sfrac false 12 1))
      (p22406 (Eq.refl true) (Eq.refl true)
        (p22173 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p22755 (Eq.refl true)))

noncomputable def p22777 :=
@p22768 false p22540 p22541 p22769
  p22770 p22540 p22541 p22542
  p20578 (p22776 (Eq.refl true)) (Eq.refl true)

noncomputable def p22778 :=
@p22544 p22532 p20578
  (@p22552 p22539 p20904
    (p22644 (Eq.refl true)) p22767 (Eq.refl true)
    (Eq.refl true))
  p22777 (Eq.refl true) (Eq.refl true)

noncomputable def p22779 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p22492
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
        (Enclosure.sfrac false 12 1))))
  true p22533

noncomputable def p22780 :=
nat_lit
  33331180333666646934136786619778640766210192326023978132527100869518964796934432959698634935990448033607835554987701330076725160026458770735343981252313272912355923910465743150019972747363084271530883344572846018122883475581454089694929980342319631524059388817998630761796852238743802557280229893071169113599

noncomputable def p22781 :=
nat_lit
  139119100835586029475560562115172963969207286956830253553039883144085686347198668582538978923850926678912684075421303017891733403200129204766462422548480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p22782 :=
nat_lit
  935189241222239872095873493995211356868919395452759746809190104685606122397854813775960136554696232794436624579530742955545065256170522466132692307093115806417971791521457

noncomputable def p22783 :=
nat_lit
  3773962424821541352241554580988268890916921220416440428376206300245624162392148852086126725177658767541468375030763844899770584629924792632561434251432696043649395326976

noncomputable def p22784 :=
nat_lit
  63601903853335253720822538499430938325196542967199858428293747320918656382058896810996207344286923037030498609126291182542482946339846712374491079567807227584055659877284652896147189965335604965005063508616880486220228664143848965184427349657042287985836649319873509941

noncomputable def p22785 :=
@Enclosure.Real.IsNear.mulLit_tf p22492
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
      (Enclosure.sfrac false 12 1)))
  p22782 p22783 p22784

noncomputable def p22786 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 8 1)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) Real.pi Real.pi) Real.pi))
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
        (Enclosure.sfrac false 12 1))))

noncomputable def p22787 :=
@p22786 p20559 p13788 p20560
  p20561 8998126516260709 9007199254740992 873417841
  59813432551014400000000 p22782 p22783 p22784

noncomputable def p22788 :=
@p22787 p21235 d268
  (@p22662 17996253032521418 18014398509481984 468912632854740992
    p20927 8998126516260709 9007199254740992 873417841
    59813432551014400000000
    (p22664 (p22673 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p22789 :=
@p22785 p21235 p22747 p22748
  p22749 p22750 p22533 p21002
  p22780 p22781 (p22788 (Eq.refl true))
  (@p22405 false p22747 p22748 p22749
    p22750
    (BSN.correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
        (Enclosure.sfrac false 12 1))
      (p22406 (Eq.refl true) (Eq.refl true)
        (p22173 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p22753 (Eq.refl true)))

noncomputable def p22790 :=
p22536 p22778
  (@p22779 p21002 p22780 p22781
    p22533 p21002 p22534 p20578
    (p22789 (Eq.refl true)) (Eq.refl true))
  (Eq.refl true)

noncomputable def p22791 :=
p22500
  (p22501
    (@Enclosure.Real.IsNear.neg p22411 false 401457751629956851
      18014398509481984 130643 18014398509481984
      (p22529 (Eq.refl true))))
  (p22790 (Eq.refl true)) (Eq.refl true)

noncomputable def p22792 :=
@p22494 false p22478 p22479 p22495
  p20899 p22478 p22479 p22480
  p20924 p22791 (Eq.refl true)

noncomputable def p22793 :=
@p22481 p22476
  (@p22493 false p22478 p22479 p22480
    p20924
    (BSN.iteratedDeriv_three_correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
        (Enclosure.sfrac false 12 1))
      (p22406 (Eq.refl true) (Eq.refl true)
        (p22173 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    p22792)

noncomputable def p22794 :=
@Enclosure.Real.IsNear.recentre' p22473 false p22468 p22469
  p22475 p22476 p22468 p22469
  p22471 p22472
  (p22793 d269 (Eq.refl true))

noncomputable def p22795 :=
@p22470 p22471 p22472 1348196141 17179869184
  1 17179869184 p22398 p22372 p22467
  p20890
  (@p22474 p22469 p22471 p22472
    (BSN.correctionLinear_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22170
        (Enclosure.sfrac false 12 1)))
    (@Enclosure.Real.IsNear.neg p22473 false p22468 p22469
      p22471 p22472 (p22794 (Eq.refl true))))

noncomputable def p22796 :=
@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv p22170) false
  1348196141 17179869184 1 17179869184 1348196141
  17179869184

noncomputable def p22797 :=
@Enclosure.Real.IsNear.inv_image p22170 218920597879 17179869184 41
  17179869184 674098070 674098071 8589934592
  (p22389 (Eq.refl true)) (Eq.refl true) (Eq.refl true)

noncomputable def p22798 :=
@p22466 p22398 p22372 p22467
  p20890 p22398 p22372 p22399
  p22400
  (p22795
    (@p22796 1 17179869184
      (p22797 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (Eq.refl true))
    (Eq.refl true))

noncomputable def p22799 :=
@p22393 false p22371 p22372 p22394
  p22395 p22371 p22372 p22373
  p20904
  (p22465 (p22798 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p22800 :=
@p22374 p22368
  (@p22376 17179869184
    (@p2563 1 0 1
      (BSN.neg_one_pow_even_mk 12 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1))
    p22392 (Eq.refl true))
  p22799 (Eq.refl true)

noncomputable def p22801 :=
@Enclosure.Real.IsNear.recentre' p22171 false p22367 p22368
  p22369 p22368 p22178 p20575
  p22179 p22175 p22800

noncomputable def p22802 :=
@p22172 p20575 p22165 p20578
  (BSN.hardyZApproximantRS_eq
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
      true 5)
    12
    (p22173 (Eq.refl true) (Eq.refl true)
      (Eq.refl true)))
  (p22176
    (p22366 (p22801 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))

theorem d280 : p22164 p22165 p20578 :=
@p22166 p20575 p22165 p20578
  (@Eq.refl Real
    (hardyZApproximantRS
      (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
        true 5)))
  p22802

theorem d281 : Enclosure.Real.IsNear Real.pi false p2138 p2102 1
  p2139 :=
d102

theorem d282 : p20540 p20541 :=
@p20542 1 p2139 p20538 p20539
  1 p20541 (Enclosure.Real.IsNear.const false 2 1) d281
  (Eq.refl true)

noncomputable def p22803 :=
Enclosure.Real.IsNear
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi))
  false 187896992210048078495 1180591620717411303424

noncomputable def p22804 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi))
  false 187896992210048078495 1180591620717411303424

noncomputable def p22805 :=
@p22804 1 1180591620717411303424 187896992210048078495
  1180591620717411303424 1 1180591620717411303424
  (@p20545 93948496105024039247 93948496105024039248
    590295810358705651712 d282 (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true))

theorem d283 : p22803 1 1180591620717411303424 :=
p22805 (Eq.refl true)

theorem d284 : p20547 p20548 :=
@p20549 1 p2139 p20538 p2930
  1 p20548 (Enclosure.Real.IsNear.const false 4 1) d281
  (Eq.refl true)

theorem d285 : p20552 p20553 :=
@p20554 p8045 p20551 p20553 d281
  d281 (Eq.refl true)

noncomputable def p22806 :=
@p2321 p20550 p8045 p20551
  p20553 p20550 p20555 p20551
  p20557 (Enclosure.Real.IsNear.const false 4 1) d285
  (Eq.refl true)

theorem d286 : p20556 p20551 p20557 :=
p22806

noncomputable def p22807 :=
@p20564 p20553 p2138 p2102 1
  p2139 p20559 p5674 p20560
  p20562 d285 d281

theorem d287 : p2323 p20559 p13788 p20560
  p20561 :=
p20563 (p22807 (Eq.refl true)) (Eq.refl true)

noncomputable def p22808 :=
Enclosure.Real.IsNear
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 96 1)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) Real.pi Real.pi)))
  false 1246030629263687631

noncomputable def p22809 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 96 1)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) Real.pi Real.pi)))
  false 1246030629263687631

noncomputable def p22810 :=
@p2337 p20550 p8045 p20551
  p20553 p20568 p2848 p20569
  p20571 (Enclosure.Real.IsNear.const false 96 1) d285
  (Eq.refl true)

noncomputable def p22811 :=
@p20570 p20571 623015314631843815 623015314631843816
  590295810358705651712 p22810 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

theorem d288 : p22808 1180591620717411303424 1 1180591620717411303424 :=
@p22809 1180591620717411303424 1 1180591620717411303424
  1246030629263687631 1180591620717411303424 1 1180591620717411303424
  p22811 (Eq.refl true)

noncomputable def p22812 :=
nat_lit
  149644795015846342922326501405433504323416958891915184784110835195669953728315147838563300494405149397178597665404806683069796037803588561396236970265187369205446322499300946766491596852138418687298848506021904774637221740475206721863215824110141572363307344088930640091821456973570114880356980151861563223769

noncomputable def p22813 :=
Enclosure.Real.IsNear
  (hardyZApproximantRS
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
      true 5))
  true p22812 p20588

noncomputable def p22814 :=
nat_lit
  4994747855634346958347168706613871442533542769263472946579088302960076159045938234342934035788234867328031544188543994112663298336455687179540554136429815827491815430236899157091432751019304642609289971130760859773913397954433655666049995639174928755680234758830951410192606471439087573641479526748819629

noncomputable def p22815 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZApproximantRS
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
      true 5))
  (hardyZApproximantRS
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
      true 5))
  true p22812

noncomputable def p22816 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
  (Zeta.RiemannSiegel.mainSumOfPhase
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
        true 5))
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
      true 5)
    12)

noncomputable def p22817 :=
@HPow.hPow Real Real Real (@instHPow Real Real Real.instPow)
  (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
      true 5)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@OfNat.ofNat Real 2
        (@instOfNatAtLeastTwo Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p22818 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  (@HPow.hPow Real Nat Real
    (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))
    (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)))
    12)
  (p22817
    (@Neg.neg Real Real.instNeg
      (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
        (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))
        (@OfNat.ofNat Real 4
          (@instOfNatAtLeastTwo Real 4 Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 3 (instOfNatNat 3))
              (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 2 (instOfNatNat 2)))))))))

noncomputable def p22819 :=
Real.sqrt
  (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
      true 5)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@OfNat.ofNat Real 2
        (@instOfNatAtLeastTwo Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p22820 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p22818
  (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
        (Enclosure.sfrac false 12 1)))
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Zeta.RiemannSiegel.correctionLinear
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
          (Enclosure.sfrac false 12 1)))
      (@Inv.inv Real Real.instInv p22819)))

noncomputable def p22821 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZApproximantRS
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
      true 5))
  (p22816 p22820) true p22812

noncomputable def p22822 :=
@BSN.floor_sqrt_eq_dec
  (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
    true 5)
  102149700 100000 12
  (Enclosure.sfrac_ofScientific_eq 102149700 5 100000 (Eq.refl true))

noncomputable def p22823 :=
@Enclosure.Real.IsNear.subLit_ff_n
  (Zeta.RiemannSiegel.mainSumOfPhase
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
        true 5))
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
      true 5)
    12)

noncomputable def p22824 :=
nat_lit
  201266682399958847455010705393521069166931152190811555590504034107049840172929935154260035673526104998574052659821864991003079886534595666545952197988022580895095605362378391816920671516663027936841547349748162314845482844456897847417312622695053864466314544498484930007296429409862514845812049500180519186137

noncomputable def p22825 :=
nat_lit
  2700798608546434193038599048848931628876185264953571583705565498857519139204014440227221912765850992306900542472941737671209912222094243293858637110808995160677604799506364768861013161937084670727402639462480136695982960950132652326801453445781571294367777750408730199095741169276768307450073691419873453

noncomputable def p22826 :=
nat_lit
  5141756004877470756900747134163479502174003563300416939628422860837185696583574633184275705994325981079009533152444762439896086942054340341092207078040833584397355681743732393791346857110008447416830439294580320533544941117129698953935041199541970841843379786068608118453756758180438238192769460460532220524193478868992

noncomputable def p22827 :=
@p22823 p22820 1233326833 34359738368 27403
  8589934592 p22824 p20588 p22825
  p22175 p22826 p22812

noncomputable def p22828 :=
@Enclosure.Real.IsNear.of_eq
  (Zeta.RiemannSiegel.mainSumOfPhase
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
        true 5))
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
      true 5)
    12)

noncomputable def p22829 :=
@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
        true 5))
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
      true 5)
    12)

noncomputable def p22830 :=
p22829
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
        true 5))
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
      true 5)
    12)

noncomputable def p22831 :=
@p22828 p22830 false 1233326833 34359738368 27403
  8589934592
  (BSN.main_sum_of_phase_eq
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
        true 5))
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
      true 5)
    12)

noncomputable def p22832 :=
@Enclosure.Real.IsNear.addLit_ff
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
        true 5))
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
      true 5)
    12)

noncomputable def p22833 :=
@p22832
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
        true 5))
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
      true 5)
    12)

noncomputable def p22834 :=
@p22833 2466653666 137438953472 219224 137438953472
  2466653666 137438953472 219224 137438953472 678028596865824456704
  1233326833 34359738368

noncomputable def p22835 :=
BSN.mainSumRS_step
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
      true 5))
  (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
    true 5)
  Real.sin BSN.quadSignNeg

noncomputable def p22836 :=
p22835 11 12 102149700 100000 285
  137438953472 68719476736 2305843009213693952 false 287131239011640
  3345

noncomputable def p22837 :=
p22836 341522969406 43 39675208392 8 false
  42021890997 205568 true 205197735060 7244019458077122842 1

noncomputable def p22838 :=
p22837 false 137023361524 true false 2466653666 219224
  BSN.abs_quadSignNeg (BSN.cos_quad_nat1 285 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 137023361524 137438953472)
  (Enclosure.sfrac_ofScientific_eq 102149700 5 100000 (Eq.refl true))
  (Eq.refl true)

noncomputable def p22839 :=
BSN.mainSumRS_step2
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
      true 5))
  (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
    true 5)
  Real.sin Real.sin

noncomputable def p22840 :=
p22839 BSN.quadSignPos BSN.quadSignNeg 9 10 11 102149700
  100000 167 229 137438953472 68719476736

noncomputable def p22841 :=
p22840 2305843009213693952 false 287131239011640 3345
  316464885454 43 43462013224 8 329564216814 43
  41439403656

noncomputable def p22842 :=
p22841 8 false 39826753431 176349 true 83295338481
  true 79129621841 7244019458077122842 1 false

noncomputable def p22843 :=
p22842 78289096116 false false 74829849064 true false
  42021890997 205568 BSN.abs_quadSignPos
  (BSN.cos_quad_nat3 167 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 78289096116 137438953472)

noncomputable def p22844 :=
BSN.mainSumRS_step2
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
      true 5))
  (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
    true 5)
  Real.cos Real.cos

noncomputable def p22845 :=
p22844 BSN.quadSignNeg BSN.quadSignNeg 7 8 9 102149700
  100000 22 98 137438953472 68719476736

noncomputable def p22846 :=
p22845 2305843009213693952 false 287131239011640 3345
  285796269294 43 48592008000 16 301984246446 43
  45812984488

noncomputable def p22847 :=
p22846 8 false 93310980140 143853 true 59243411381
  true 187679659519 7244019458077122842 1 false

noncomputable def p22848 :=
p22847 124866927078 true false 28011303802 true false
  39826753431 176349 BSN.abs_quadSignNeg
  (BSN.cos_quad_nat2 22 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 124866927078 137438953472)

noncomputable def p22849 :=
p22844 BSN.quadSignPos BSN.quadSignPos 5 6 7 102149700
  100000 164 64 137438953472 68719476736

noncomputable def p22850 :=
p22849 2305843009213693952 false 287131239011640 3345
  246257546308 43 56109217800 8 267443854420 43
  51947041624

noncomputable def p22851 :=
p22850 8 false 43534443293 106669 false 174163293991
  false 121273443742 7244019458077122842 1 false

noncomputable def p22852 :=
p22851 41087301250 false false 87316980051 false false
  93310980140 143853 BSN.abs_quadSignPos
  (BSN.cos_quad_nat0 164 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 41087301250 137438953472)

noncomputable def p22853 :=
BSN.mainSumRS_step2
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
      true 5))
  (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
    true 5)
  Real.cos Real.sin

noncomputable def p22854 :=
p22853 BSN.quadSignPos BSN.quadSignPos 3 4 5 102149700
  100000 428 283 137438953472 68719476736

noncomputable def p22855 :=
p22854 2305843009213693952 false 287131239011640 3345
  190530846192 42 68719476728 8 221199462352 42
  61464568544

noncomputable def p22856 :=
p22855 16 true 40210076651 62834 false 104229018483
  false 80177091383 7244019458077122842 1 false

noncomputable def p22857 :=
p22856 99775291900 false false 75706271770 false false
  43534443293 106669 BSN.abs_quadSignPos
  (BSN.cos_quad_nat0 428 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 99775291900 137438953472)

noncomputable def p22858 :=
p22839 BSN.quadSignPos BSN.quadSignPos 1 2 3 102149700
  100000 879 615 137438953472 68719476736

noncomputable def p22859 :=
p22858 2305843009213693952 false 287131239011640 3345
  95265423088 42 97184016000 16 150992123216 42
  79350416784

noncomputable def p22860 :=
p22859 16 true 137437629176 3393 false 51812847119
  false 121747110368 7244019458077122842 1 false

noncomputable def p22861 :=
p22860 50594264931 false false 106437994373 false true
  40210076651 62834 BSN.abs_quadSignPos
  (BSN.cos_quad_nat3 879 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 50594264931 137438953472)

noncomputable def p22862 :=
@Enclosure.Real.IsNear.recentre'
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
        true 5))
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
      true 5)
    1)

noncomputable def p22863 :=
@Enclosure.Real.IsNear.of_eq
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
        true 5))
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
      true 5)
    1)

noncomputable def p22864 :=
@p22863
  (Real.cos
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
        true 5)))
  true 17179703647

noncomputable def p22865 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
        true 5)))
  true 17179703647

noncomputable def p22866 :=
@Enclosure.Real.IsNear.cos_image
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
      true 5))
  (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
    (@Nat.cast Real Real.instNatCast 35891404876455)
    (@Nat.cast Real Real.instNatCast 17179869184))
  false 35891404876455

noncomputable def p22867 :=
nat_lit 42757593734632766409289153277200861195217909811658229522287

noncomputable def p22868 :=
nat_lit 20466456231293690186301117234110254778500814875918336000

noncomputable def p22869 :=
@Enclosure.Real.IsNear.recentre'
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
      true 5))
  false p22867 p22868

noncomputable def p22870 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 102149700 400000)
      (Real.log (Enclosure.sfrac false 41738254840360000 160000000000)))
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 1 4)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 1 2) Real.pi)
        (Real.arctan
          (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
            (@Nat.cast Real Real.instNatCast 100000)
            (@Nat.cast Real Real.instNatCast 204299400))))))

noncomputable def p22871 :=
nat_lit 533859503844079560977754771483360000000000000000

noncomputable def p22872 :=
nat_lit 3272015655426997889717989222670842739520000000000000

noncomputable def p22873 :=
@Enclosure.Real.IsNear.of_eq
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
      true 5))
  (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (p22870 (Enclosure.sfrac false 102149700 200000))
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 102149700 200000) (Real.log Real.pi)))
    (Enclosure.sfrac true p22871 p22872))
  false

noncomputable def p22874 :=
BSN.riemannSiegelThetaApproximant_two_zero_mk
  (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
    true 5)
  102149700 100000 41738254840360000 160000000000

noncomputable def p22875 :=
p22874 204299400 400000 200000 p22871
  p22872
  (Enclosure.sfrac_ofScientific_eq 102149700 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p22876 :=
@Enclosure.Real.IsNear.addLit_ft_p
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (p22870 (Enclosure.sfrac false 102149700 200000))
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 102149700 200000) (Real.log Real.pi)))
  (Enclosure.sfrac true p22871 p22872) 37634868698948877145903
  18014398509481984000

noncomputable def p22877 :=
nat_lit 123141869955742367258752761438338480242227580257575701024186560000000000000

noncomputable def p22878 :=
@p22876 867451804390581429 p20639 p22871
  p22872 0 1 p22877 p22867
  p22868 867451804390581429 p20639

noncomputable def p22879 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (p22870 (Enclosure.sfrac false 102149700 200000))
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 102149700 200000) (Real.log Real.pi))
  48167330359892323718959 18014398509481984000 643730846133 68000000000000000000

noncomputable def p22880 :=
nat_lit 5172496968039663901362406572425216000

noncomputable def p22881 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 102149700 400000)
      (Real.log (Enclosure.sfrac false 41738254840360000 160000000000)))
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 1 4)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 1 2) Real.pi)
        (Real.arctan
          (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
            (@Nat.cast Real Real.instNatCast 100000)
            (@Nat.cast Real Real.instNatCast 204299400))))))

noncomputable def p22882 :=
@p22881 (Enclosure.sfrac false 102149700 200000)
  57368157377012482823983 18014398509481984000 643730846133 68000000000000000000
  102149700 200000 0

noncomputable def p22883 :=
nat_lit 9633466071978464743791800000

noncomputable def p22884 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 102149700 400000)
    (Real.log (Enclosure.sfrac false 41738254840360000 160000000000)))
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 1 4)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 1 2) Real.pi)
      (Real.arctan
        (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
          (@Nat.cast Real Real.instNatCast 100000)
          (@Nat.cast Real Real.instNatCast 204299400)))))
  57375229410353147935983

noncomputable def p22885 :=
nat_lit 129181606093022694427993681145347702784

noncomputable def p22886 :=
@p22884 18014398509481984000 638730837633 68000000000000000000
  884004167583139 2251799813685248 10000017 136000000000000000
  p22885 57368157377012482823983 18014398509481984000 643730846133

noncomputable def p22887 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 102149700 400000)
  (Real.log (Enclosure.sfrac false 41738254840360000 160000000000)) 102149700
  400000 0 1 56167790419700839 4503599627370496

noncomputable def p22888 :=
nat_lit 30878569336473243853921452032

noncomputable def p22889 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
      (@Nat.cast Real Real.instNatCast 41738254840360000)
      (@Nat.cast Real Real.instNatCast 160000000000)))
  false p22888 p2333

noncomputable def p22890 :=
BSN.log_rat_reduce_isNear 41738254840360000 160000000000 17 83476509680720000
  41943040000000000 47296369786 68719476736 24973259072661432
  36028797018963968 27200000000 1000000000000000

noncomputable def p22891 :=
nat_lit
  1099978178980550333249349305284367931389604260465982857377919769578272294811448644649820718640992932626332940145593406979469882518829598412928905573711747593767624869741381844479730321686067210553771560071354196533072983537582611372049193658528980111734143865689651923087050033114906305232896000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p22892 :=
nat_lit
  43081912028328270049402208032112711927041311630187894972088830792052939250965169076920779508096738287342540981772295577740128044229417569999030422604676694419021964023515849497788162587941242353520353125506036007512265320214058201427574296527400111767182512008335873452051260463526620797337600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p22893 :=
nat_lit
  1319415891474147286965727223877665926947106373624730711627871499116976870985040775839514088159918718567539755975950783970916243400902689821052136195925192465023117744403304187062131624378913205993094515196543888556666194239413982194370163495224042154907737422042494679509423357952000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p22894 :=
BSN.log_dyadic_bound 20766734840360000 62709774840360000 12 11
  p22891 68719476736 27200000000 p22892 p22893
  47296369786 83476509680720000

noncomputable def p22895 :=
p22894 41943040000000000 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p22896 :=
@BSN.binarySplit_of_base11 (BSN.artanhP 20766734840360000) (BSN.artanhQ 62709774840360000)
  0 11 p22892 p22891 p22893
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p22897 :=
p22890 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p22895 (p22896 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

noncomputable def p22898 :=
@p22887 625289 17000000000000000 57375229410353147935983
  18014398509481984000 638730837633 68000000000000000000
  (Enclosure.Real.IsNear.const false 102149700 400000)
  (BSN.isNear_log_sfrac 41738254840360000 160000000000 56167790419700839
    4503599627370496 625289 17000000000000000 false
    (@p22889 1000462400000000 p20660 56167790419700839
      4503599627370496 625289 17000000000000000
      (p22897 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p22899 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 1 4)
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 1 2) Real.pi)
    (Real.arctan
      (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
        (@Nat.cast Real Real.instNatCast 100000)
        (@Nat.cast Real Real.instNatCast 204299400))))
  1 4

noncomputable def p22900 :=
@p22899 0 1 884004167583139 562949953421312 10000017
  34000000000000000 884004167583139 2251799813685248 10000017
  136000000000000000 (Enclosure.Real.IsNear.const false 1 4)

noncomputable def p22901 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 1 2) Real.pi)
  (Real.arctan
    (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
      (@Nat.cast Real Real.instNatCast 100000) (@Nat.cast Real Real.instNatCast 204299400)))
  884279719003555 562949953421312 1

noncomputable def p22902 :=
nat_lit 7593537978594570732044288

noncomputable def p22903 :=
@p22901 2000000000000000 4204581 8589934592 1
  3400000000 p22902 884004167583139 562949953421312 10000017
  34000000000000000
  (@p803 1 1000000000000000 884279719003555 562949953421312
    1 2000000000000000 (Enclosure.Real.IsNear.const false 1 2)
    BSN.pi_near_15 (Eq.refl true))

noncomputable def p22904 :=
BSN.arctan_dyadic_bound_f 100000 204299400 1 0 8589934592
  3400000000 0 1 1 0 1

noncomputable def p22905 :=
p22904 1 4204581 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)
  (@BSN.binarySplit_of_le (BSN.arctanEvenP 100000) (BSN.arctanEvenQ 204299400) 0
    0 (Eq.refl true))
  (@BSN.binarySplit_of_le (BSN.arctanOddP 100000) (BSN.arctanOddQ 204299400) 0 0
    (Eq.refl true))

noncomputable def p22906 :=
p22900
  (p22903
    (p22905 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p22907 :=
@p22879 80356305396602223 137438953472000 1021497
  68719476736000 p22880 37634868698948877145903 18014398509481984000
  867451804390581429 p20639
  (@p22882 1 p22883 48167330359892323718959
    18014398509481984000 643730846133 68000000000000000000
    (@p22886 68000000000000000000 p22898 p22906
      (Eq.refl true) (Eq.refl true))
    (Enclosure.Real.IsNear.const false 102149700 200000) (Eq.refl true)
    (Eq.refl true))

noncomputable def p22908 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 102149700 200000) (Real.log Real.pi)
  102149700 200000 0 1 78665238759 68719476736

noncomputable def p22909 :=
p22907
  (@p22908 1 34359738368 80356305396602223 137438953472000
    1021497 68719476736000
    (Enclosure.Real.IsNear.const false 102149700 200000) d258
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p22910 :=
@p22866 17179869184 419 17179869184 true 17179703647
  17179869184 1 3400000000
  (@p22869 867451804390581429 p20639 35891404876455
    17179869184 419 17179869184
    (@p22873 p22867 p22868 867451804390581429
      p20639
      (p22875 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p22878 (p22909 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p22871 p22872)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p22911 :=
nat_lit 3878234515204484990112890880

noncomputable def p22912 :=
BSN.cos_reduce1
  (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
    (@Nat.cast Real Real.instNatCast 35891404876455)
    (@Nat.cast Real Real.instNatCast 17179869184))
  (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
    (@Nat.cast Real Real.instNatCast p22911)
    (@Nat.cast Real Real.instNatCast p2333))
  226375608064910080 72057594037927936 false

noncomputable def p22913 :=
BSN.sin_reduce_arg_pos_rat_q1 35891404876455 17179869184 226375608064910080
  72057594037927936 332 p22911 p2333
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p22914 :=
nat_lit
  1126623041797716936011540870394242243141379924457309370980015372614088631808200874560334067087910016410825667117997380945868738841753236506328527879558976532319349868855296

noncomputable def p22915 :=
nat_lit
  785328211848775143562597560658103523293918001120527895824138239836107571589824699334848793727298546582181813013790103230250667125674330465920699273070848383853264896

noncomputable def p22916 :=
nat_lit
  5626193170639364578589292796533485403845272646948921694505642240121652242122047977191979290617648559956000440587886154161726513193333843385349752797217294968649913158598656

noncomputable def p22917 :=
BSN.sin_dyadic_bound_f 55113027247052 35184372088832 4 3 17179869184
  6806640626 p22914 p3100 p22915
  p22916 p3103

noncomputable def p22918 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 55113027247052) (BSN.sinEvenQ 35184372088832) 0
  3 p22914 p3100 p22915 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p22919 :=
p22917 p22915 17179703647 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p22918 (Eq.refl true))

noncomputable def p22920 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 55113027247052) (BSN.sinOddQ 35184372088832) 0
  3 p22916 p3103 p22915 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p22921 :=
@BSN.sin_arg_round false 17179703647 17179869184 p22911
  p2333 55113027247052 35184372088832 6806640626 6800000000
  (p22919 (p22920 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p22922 :=
p22912 17179703647 17179869184 332 1000000000000000
  6800000000 3400000000 p22913 BSN.pi_near_15 p22921
  (Eq.refl true) (Eq.refl true)

noncomputable def p22923 :=
@p22864 17179869184 2815976307 114085068800000000
  (BSN.main_sum_rs_one
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
        true 5))
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
      true 5))
  (@p22865 17179869184 1441779869184 58411555225600000000
    17179703647 17179869184 2815976307 114085068800000000
    (p22910 (Enclosure.sfrac_false_div 35891404876455 17179869184)
      (p22922 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p22924 :=
@p22862 true 17179703647 17179869184 2815976307
  114085068800000000 137437629176 137438953472 3393 137438953472
  p22923 (Eq.refl true)

noncomputable def p22925 :=
p22861 BSN.abs_quadSignPos (BSN.cos_quad_nat3 615 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 106437994373 137438953472)
  (Enclosure.sfrac_ofScientific_eq 102149700 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true) p22924
  (@p22869 867451804390581429 p20639 287131239011640
    137438953472 3345 137438953472
    (@p22873 p22867 p22868 867451804390581429
      p20639
      (p22875 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p22878 (p22909 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p22871 p22872)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p22926 :=
nat_lit 7776315557720029761793809411597238475481899095579099543234521962906078756544600012441070465

noncomputable def p22927 :=
nat_lit 51939726640496959714784502169725588615280645959216434308871937031653929994245930298241

noncomputable def p22928 :=
nat_lit 20366456653518850476287105474513064070547215748327993405672962205427393113158723634410892161

noncomputable def p22929 :=
BSN.sin_dyadic_bound_f 51812847119 137438953472 3 2 137438953472
  68719476736 p22926 p2477 p22927
  p22928 p2480

noncomputable def p22930 :=
@BSN.binarySplit_of_base2 (BSN.sinEvenP 51812847119) (BSN.sinEvenQ 137438953472) 0
  2 p22926 p2477 p22927 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p22931 :=
p22929 p22927 50594264931 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p22930 (Eq.refl true))

noncomputable def p22932 :=
@BSN.binarySplit_of_base2 (BSN.sinOddP 51812847119) (BSN.sinOddQ 137438953472) 0
  2 p22928 p2480 p22927 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p22933 :=
nat_lit
  1451780167559816627008854772088834733344109776368637807789340309108899728624440069126882181755737560952057028830842663335457871207355463499776

noncomputable def p22934 :=
nat_lit
  10604835735908294822975871296664327710402060869235743936145739647163292307363452997839126743230440585653886324615009514095264531480576

noncomputable def p22935 :=
nat_lit
  7257987287766976625110689102824858039531430804779961435227200718959146996813872787622805415770251475565376546716278097745302142092699643150336

noncomputable def p22936 :=
BSN.sin_dyadic_bound_f 121747110368 137438953472 4 3 137438953472
  68719476736 p22933 p2504 p22934
  p22935 p2507

noncomputable def p22937 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 121747110368) (BSN.sinEvenQ 137438953472) 0
  3 p22933 p2504 p22934 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p22938 :=
p22936 p22934 106437994373 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p22937 (Eq.refl true))

noncomputable def p22939 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 121747110368) (BSN.sinOddQ 137438953472) 0
  3 p22935 p2507 p22934 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p22940 :=
p22925 d93 d95 d97 d99 d103
  (p22931 (p22932 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p22938 (p22939 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p22941 :=
p22857 BSN.abs_quadSignPos (BSN.cos_quad_nat3 283 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 75706271770 137438953472)
  (Enclosure.sfrac_ofScientific_eq 102149700 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p22940 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p22869 867451804390581429 p20639 287131239011640
    137438953472 3345 137438953472
    (@p22873 p22867 p22868 867451804390581429
      p20639
      (p22875 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p22878 (p22909 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p22871 p22872)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p22942 :=
nat_lit
  299947005049298534524196020700561710645482209198087604584343950052062162079582762886313624925992342670117394494526891658867262722909497630641

noncomputable def p22943 :=
nat_lit
  1643856021395908933665599766834833516782116188778081512780484554576527424343501790790541285155030008855863124248209210808516695203761

noncomputable def p22944 :=
nat_lit
  1819439694724285492762545633001717912238886829893665615281210491707451813135603990359785468818389818332246010910276790989881682499789150920625

noncomputable def p22945 :=
BSN.cos_dyadic_bound_f 104229018483 137438953472 4 3 137438953472
  68719476736 p22942 p2457 p22943
  p22944 p2460

noncomputable def p22946 :=
@BSN.binarySplit_of_base3 (BSN.cosEvenP 104229018483) (BSN.cosEvenQ 137438953472) 0
  3 p22942 p2457 p22943 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p22947 :=
p22945 p22943 99775291900 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p22946 (Eq.refl true))

noncomputable def p22948 :=
@BSN.binarySplit_of_base3 (BSN.cosOddP 104229018483) (BSN.cosOddQ 137438953472) 0
  3 p22944 p2460 p22943 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p22949 :=
nat_lit 44590153359926480706348369436625496931410142270520178768594365711080375805998089646531923265

noncomputable def p22950 :=
nat_lit 1707663819170638029368785148595276379039396851316595130802713935461318131977110972779841

noncomputable def p22951 :=
nat_lit 116780970201243077959817227634254766277650975494555479430392515325505475453019414704103869761

noncomputable def p22952 :=
BSN.sin_dyadic_bound_f 80177091383 137438953472 3 2 137438953472
  68719476736 p22949 p2477 p22950
  p22951 p2480

noncomputable def p22953 :=
@BSN.binarySplit_of_base2 (BSN.sinEvenP 80177091383) (BSN.sinEvenQ 137438953472) 0
  2 p22949 p2477 p22950 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p22954 :=
p22952 p22950 75706271770 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p22953 (Eq.refl true))

noncomputable def p22955 :=
@BSN.binarySplit_of_base2 (BSN.sinOddP 80177091383) (BSN.sinOddQ 137438953472) 0
  2 p22951 p2480 p22950 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p22956 :=
p22941 d105 d107 d109 d111 d103
  (p22947 (p22948 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p22954 (p22955 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p22957 :=
p22852 BSN.abs_quadSignPos (BSN.cos_quad_nat0 64 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 87316980051 137438953472)
  (Enclosure.sfrac_ofScientific_eq 102149700 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p22956 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p22869 867451804390581429 p20639 287131239011640
    137438953472 3345 137438953472
    (@p22873 p22867 p22868 867451804390581429
      p20639
      (p22875 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p22878 (p22909 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p22871 p22872)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p22958 :=
nat_lit
  2341516312120261835050449283319088204949985355976553842003666617801938876547455039609035346903596918696541299967571756512415499259074753625761

noncomputable def p22959 :=
nat_lit
  778896155575308954539828785702629141382148523099477684411325211390672452926742062977822869790913856771302684060736146293774300100984481

noncomputable def p22960 :=
nat_lit
  14190681662298718189858087128678380137839348232742950887034413075580874212349549010365474941294607930518701230621329112421528797660698297532065

noncomputable def p22961 :=
BSN.cos_dyadic_bound_f 174163293991 137438953472 4 3 137438953472
  68719476736 p22958 p2457 p22959
  p22960 p2460

noncomputable def p22962 :=
@BSN.binarySplit_of_base3 (BSN.cosEvenP 174163293991) (BSN.cosEvenQ 137438953472) 0
  3 p22958 p2457 p22959 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p22963 :=
p22961 p22959 41087301250 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p22962 (Eq.refl true))

noncomputable def p22964 :=
@BSN.binarySplit_of_base3 (BSN.cosOddP 174163293991) (BSN.cosOddQ 137438953472) 0
  3 p22960 p2460 p22959 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p22965 :=
nat_lit
  549824350724375293569976074657188412543195310865891967678424781013028213254853716733582393645975340793173719605873641719185285688433234415616

noncomputable def p22966 :=
nat_lit
  10120186647016910109764770206955306581357281643887604231767933111069552284986988699122555687395929669849739970634202314270999625076736

noncomputable def p22967 :=
nat_lit
  3334798887921084017112754486575841355042496049628042090381881669174372417292495432802109923467796121405225471147823732341260116188254395699200

noncomputable def p22968 :=
BSN.cos_dyadic_bound_f 121273443742 137438953472 4 3 137438953472
  68719476736 p22965 p2457 p22966
  p22967 p2460

noncomputable def p22969 :=
@BSN.binarySplit_of_base3 (BSN.cosEvenP 121273443742) (BSN.cosEvenQ 137438953472) 0
  3 p22965 p2457 p22966 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p22970 :=
p22968 p22966 87316980051 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p22969 (Eq.refl true))

noncomputable def p22971 :=
@BSN.binarySplit_of_base3 (BSN.cosOddP 121273443742) (BSN.cosOddQ 137438953472) 0
  3 p22967 p2460 p22966 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p22972 :=
p22957 d113 d115 d117 d119 d103
  (p22963 (p22964 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p22970 (p22971 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p22973 :=
p22848 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 98 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 28011303802 137438953472)
  (Enclosure.sfrac_ofScientific_eq 102149700 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p22972 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p22869 867451804390581429 p20639 287131239011640
    137438953472 3345 137438953472
    (@p22873 p22867 p22868 867451804390581429
      p20639
      (p22875 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p22878 (p22909 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p22871 p22872)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p22974 :=
nat_lit 7384443941000722226844168046693180770752443337453301355919534194554012254420787294030061921

noncomputable def p22975 :=
nat_lit 151747123184557065949365319386765749812454090909325351377963708566229499760992577446241

noncomputable def p22976 :=
nat_lit 22153028328755797566400605409440768780757705104178085417055846656244904304262839896935293281

noncomputable def p22977 :=
BSN.cos_dyadic_bound_f 59243411381 137438953472 3 2 137438953472
  68719476736 p22974 p2466 p22975
  p22976 p2469

noncomputable def p22978 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP 59243411381) (BSN.cosEvenQ 137438953472) 0
  2 p22974 p2466 p22975 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p22979 :=
p22977 p22975 124866927078 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p22978 (Eq.refl true))

noncomputable def p22980 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP 59243411381) (BSN.cosOddQ 137438953472) 0
  2 p22976 p2469 p22975 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p22981 :=
nat_lit
  49237214299737388454292213806036814312225708423686099360332020381269343790814561364575679287138021624252740135515271922163082638201276637802162302525176595731645787007019845474125930053672961

noncomputable def p22982 :=
nat_lit
  2369601468266366816486934261375041536730025398106441913309347209982700463947222620819564214508126277825811101770681592172861779681169577347003181480261805523810526315693760038215681

noncomputable def p22983 :=
nat_lit
  501527781039159791182564710228273752570750289075371490794121727675848259041005331100825494167319523661650175085907314505859314267996214376679619654424125150665944294065165740962663780828487681

noncomputable def p22984 :=
BSN.cos_dyadic_bound_f 187679659519 137438953472 5 4 137438953472
  68719476736 p22981 p2495 p22982
  p22983 p2498

noncomputable def p22985 :=
@BSN.binarySplit_of_base4 (BSN.cosEvenP 187679659519) (BSN.cosEvenQ 137438953472) 0
  4 p22981 p2495 p22982 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p22986 :=
p22984 p22982 28011303802 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p22985 (Eq.refl true))

noncomputable def p22987 :=
@BSN.binarySplit_of_base4 (BSN.cosOddP 187679659519) (BSN.cosOddQ 137438953472) 0
  4 p22983 p2498 p22982 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p22988 :=
p22973 d121 d123 d125 d127 d103
  (p22979 (p22980 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p22986 (p22987 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p22989 :=
p22843 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 229 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 74829849064 137438953472)
  (Enclosure.sfrac_ofScientific_eq 102149700 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p22988 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p22869 867451804390581429 p20639 287131239011640
    137438953472 3345 137438953472
    (@p22873 p22867 p22868 867451804390581429
      p20639
      (p22875 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p22878 (p22909 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p22871 p22872)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p22990 :=
nat_lit 51942555109042853573016172802963312216130799192006672863271453607516112588507520612233812865

noncomputable def p22991 :=
nat_lit 2317210985423027942000711648371689110968234323073817738514194024740262422722588217351041

noncomputable def p22992 :=
nat_lit 136036273610659645884088641903187501640829573123494404651277165038883096354549574555879512961

noncomputable def p22993 :=
BSN.sin_dyadic_bound_f 83295338481 137438953472 3 2 137438953472
  68719476736 p22990 p2477 p22991
  p22992 p2480

noncomputable def p22994 :=
@BSN.binarySplit_of_base2 (BSN.sinEvenP 83295338481) (BSN.sinEvenQ 137438953472) 0
  2 p22990 p2477 p22991 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p22995 :=
p22993 p22991 78289096116 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p22994 (Eq.refl true))

noncomputable def p22996 :=
@BSN.binarySplit_of_base2 (BSN.sinOddP 83295338481) (BSN.sinOddQ 137438953472) 0
  2 p22992 p2480 p22991 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p22997 :=
nat_lit 42305154578574671093940795828225534740862748852901163816317055691820557815800596432506021505

noncomputable def p22998 :=
nat_lit 1537137514995131989228596536944305575734150356999824401126907479945222112233594182395521

noncomputable def p22999 :=
nat_lit 110796725673623670270433809441435633540851248847496476946085702295038692491296041027887130241

noncomputable def p23000 :=
BSN.sin_dyadic_bound_f 79129621841 137438953472 3 2 137438953472
  68719476736 p22997 p2477 p22998
  p22999 p2480

noncomputable def p23001 :=
@BSN.binarySplit_of_base2 (BSN.sinEvenP 79129621841) (BSN.sinEvenQ 137438953472) 0
  2 p22997 p2477 p22998 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p23002 :=
p23000 p22998 74829849064 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p23001 (Eq.refl true))

noncomputable def p23003 :=
@BSN.binarySplit_of_base2 (BSN.sinOddP 79129621841) (BSN.sinOddQ 137438953472) 0
  2 p22999 p2480 p22998 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p23004 :=
p22989 d129 d131 d133 d135 d103
  (p22995 (p22996 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p23002 (p23003 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p23005 :=
p22838
  (p23004 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p22869 867451804390581429 p20639 287131239011640
    137438953472 3345 137438953472
    (@p22873 p22867 p22868 867451804390581429
      p20639
      (p22875 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p22878 (p22909 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p22871 p22872)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p23006 :=
nat_lit
  11732248586672933741207937131824069678225774247137261777381080906366348882979178290651572724593706368217324470021003143746007900531353190400000

noncomputable def p23007 :=
nat_lit
  5572765307912007696273917402259702748704418908157450327165358040303895500179956977816248758532318301869835643988677154574336000000000000

noncomputable def p23008 :=
nat_lit
  58601733463070557721494460987687095838318700324611164346833554185952901223336827623843111882519735246215879237685233770990683603555581952000000

noncomputable def p23009 :=
BSN.sin_dyadic_bound_f 205197735060 137438953472 4 3 137438953472
  68719476736 p23006 p2504 p23007
  p23008 p2507

noncomputable def p23010 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 205197735060) (BSN.sinEvenQ 137438953472) 0
  3 p23006 p2504 p23007 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p23011 :=
p23009 p23007 137023361524 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p23010 (Eq.refl true))

noncomputable def p23012 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 205197735060) (BSN.sinOddQ 137438953472) 0
  3 p23008 p2507 p23007 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p23013 :=
p23005 d137 d139 d103
  (p23011 (p23012 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true) (Eq.refl true)

noncomputable def p23014 :=
@p22827 p20588 p22814 p22175
  (p22831
    (@p22834 27403 8589934592
      (p23013 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (p23013 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true) (Eq.refl true)))

noncomputable def p23015 :=
nat_lit
  432216909341121020782561905497531901179461631671567191480050397322923813292380527993473784148793976985568841404058361661042781173970739580199092985768936992326975015912368710815374151795213212020534399700601915489180502055135715568135077889341621864420618731135064747965093602846466040559538617583004238000380942429453

noncomputable def p23016 :=
nat_lit
  3088413288990945714607167766096760666649729152895234960279866913260350640380788374205938472006792060778611417607373228628384532735989280347702230834056678923362997806954442769843550227998248540363155634742320939156524772391123850992097524347673943425610505012700786888921103128284156837954503288400970554554866145951744

noncomputable def p23017 :=
nat_lit
  11599841696789240956516933780462867790563224946212684910410330310778970066575313492687664924263894917567285425045943728211257773744925463576990164038056562317732577813492473626104650699945330670357122867515431206158856311854064828605350546834898357868801994434201946838003777094924519853067339657438352283200710405

noncomputable def p23018 :=
@Enclosure.Real.IsNear.mulLit_ff p22818
  (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
        (Enclosure.sfrac false 12 1)))
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Zeta.RiemannSiegel.correctionLinear
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
          (Enclosure.sfrac false 12 1)))
      (@Inv.inv Real Real.instInv p22819)))

noncomputable def p23019 :=
nat_lit
  359340525906710454276393223465581600594826500218216994648288195871983390634013725532353434771312083652492687242100681010738247986955763810082876592716697920262863735948701401849006500348999541391957224025221362117780428682624638517332494930411621500251652596535800990832918862485227939313878828248663787538581

noncomputable def p23020 :=
nat_lit
  9643835215918472121221239393126025730802933513314969083674201745335062384426825887753584566614711161814934973465544636990806085375079913668120756707403903172423541947962412703422185325575518273826999179367950950365690417467109930604853050206951075201919406432901345174096835395624513812383815419298092727

noncomputable def p23021 :=
@p23018 1202805913 4294967296 1 8589934592
  p23019 p22175 p23020 p22175
  p23015 p23016 p23017

noncomputable def p23022 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HPow.hPow Real Nat Real
    (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))
    (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)))
    12)
  (p22817
    (@Neg.neg Real Real.instNeg
      (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
        (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))
        (@OfNat.ofNat Real 4
          (@instOfNatAtLeastTwo Real 4 Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 3 (instOfNatNat 3))
              (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 2 (instOfNatNat 2)))))))))

noncomputable def p23023 :=
@p23022 1 1 0 1 1202805913 4294967296
  1 8589934592 1202805913 4294967296 1

noncomputable def p23024 :=
@Enclosure.Real.IsNear.of_eq
  (p22817
    (@Neg.neg Real Real.instNeg
      (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
        (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))
        (@OfNat.ofNat Real 4
          (@instOfNatAtLeastTwo Real 4 Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 3 (instOfNatNat 3))
              (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 2 (instOfNatNat 2)))))))))

noncomputable def p23025 :=
BSN.rpow_neg_quarter_mk
  (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
      true 5)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@OfNat.ofNat Real 2
        (@instOfNatAtLeastTwo Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p23026 :=
p23025
  (BSN.t_div_two_pi_nonneg
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
      true 5)
    102149700 100000
    (Enclosure.sfrac_ofScientific_eq 102149700 5 100000 (Eq.refl true)))

noncomputable def p23027 :=
@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt p22819)) false
  4811223652 17179869184 2 17179869184 1202805913 4294967296

noncomputable def p23028 :=
@Enclosure.Real.IsNear.recentre' (Real.sqrt p22819) false 61345704653
  17179869184 7 17179869184 61345704653 17179869184 7
  17179869184

noncomputable def p23029 :=
@Enclosure.Real.IsNear.sqrt_image
  (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
      true 5)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@OfNat.ofNat Real 2
        (@instOfNatAtLeastTwo Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p23030 :=
@Enclosure.Real.IsNear.of_eq
  (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
      true 5)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@OfNat.ofNat Real 2
        (@instOfNatAtLeastTwo Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p23031 :=
@p23030
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 102149700 100000)
    (@Inv.inv Real Real.instInv
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)))
  false 2793039513931191

noncomputable def p23032 :=
@p23031 17179869184000 1021497 17179869184000
  (BSN.t_div_two_pi_mk
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
      true 5)
    102149700 100000
    (Enclosure.sfrac_ofScientific_eq 102149700 5 100000 (Eq.refl true)))

noncomputable def p23033 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 102149700 100000)
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi))
  102149700 100000 0

noncomputable def p23034 :=
@p23033 1 2734261103 17179869184 1 17179869184
  2793039513931191 17179869184000 1021497 17179869184000
  (Enclosure.Real.IsNear.const false 102149700 100000) d261

noncomputable def p23035 :=
@p23029 2793039513931191 17179869184000 1021497 17179869184000
  109526313570 109526313611 8589934592
  (p23032 (p23034 (Eq.refl true))) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p23036 :=
@Enclosure.Real.IsNear.recentre' p22819 false 219052627181 17179869184
  41 17179869184 219052627181 17179869184 41 17179869184
  (p23035 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p23037 :=
@Enclosure.Real.IsNear.sqrt_image p22819 219052627181 17179869184 41
  17179869184 30672852323 30672852330 8589934592
  (p23036 (Eq.refl true)) (Eq.refl true) (Eq.refl true)

noncomputable def p23038 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt p22819) 61345704653 17179869184
  7 17179869184 2405611825 2405611827 8589934592
  (p23028
    (p23037 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p23039 :=
@p23024 (@Inv.inv Real Real.instInv (Real.sqrt p22819)) false
  1202805913 4294967296 1 8589934592 p23026
  (@p23027 1 8589934592
    (p23038 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p23040 :=
@Enclosure.Real.IsNear.recentre'
  (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
        (Enclosure.sfrac false 12 1)))
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Zeta.RiemannSiegel.correctionLinear
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
          (Enclosure.sfrac false 12 1)))
      (@Inv.inv Real Real.instInv p22819)))

noncomputable def p23041 :=
nat_lit
  183982349264235752589513330414377779504551168111727101259923556286455496004615027472564958602911786830076255867955548677497982969321351070762432815470949335174586232805735117746691328178687765192682098700913337404303579485503814920874237404370750208128846129426330107306454457592436704928705960063315859219753533

noncomputable def p23042 :=
nat_lit
  368167554019802297902961703073592265444961685287384386095984806211036520049665972495786961556290633771253993225976613596485201446531925242865351537949643006725668645734124513845866945743352000756639913885870091814580532597437363981258574050387614181710541845882032738795411959682006458992302809763070411033018368

noncomputable def p23043 :=
nat_lit
  1928767043183694424244247878625205146160586702662993816734840349067012476885365177550716913322942232362986994693108927398161217075015982733624151341480780634484708389592482540684437065115103654765399835873590190073138083493421986120970610041390215040383881286580269034819367079124902762476763083859618545347068577

noncomputable def p23044 :=
nat_lit
  143815450788985272618344415263121978689438158315384525818744064926186140644400770506166781857926028816896091103897114686127031815051533297994277944511579299502214314739892388221041775680996875295562466361668004615070520545873970305179130488432661789730680408547669038591957796750783773043868285063699379309772800000000

noncomputable def p23045 :=
@Enclosure.Real.IsNear.addLit_ft_p
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
      (Enclosure.sfrac false 12 1)))
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Zeta.RiemannSiegel.correctionLinear
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
        (Enclosure.sfrac false 12 1)))
    (@Inv.inv Real Real.instInv p22819))
  73866925435965279021

noncomputable def p23046 :=
nat_lit 57646075230342348800000000

noncomputable def p23047 :=
nat_lit
  300884893883010724609842512829438756308903017112075016220730599823309191842588761165986741286848414226606590141435346997780632464248741064978269102888936458066510238279103068706371199370400777794528347009147042044434913521575731842772799157516178678034015277975259952001182239100789035230222292017004430677443

noncomputable def p23048 :=
nat_lit
  226036566868500325422509881466392795519919520616757002856119164269241128289122317659265007874517877753192672929663298965113210574103467403951116077312612618788929151172684169458791516576867699183693074980418556351173800058641266777379163650908581313094509053523509460754154868174991644454109568696984769

noncomputable def p23049 :=
nat_lit
  27151002487657614025529714552246234450460350719777395741186634620881833652007431158227407651334369810329742333767748903587489983912551442796492433643298015268991447296510765978563175522446572224384787581889361927655926550384629899912395866149938143835225760253074439235572723526611678431090987917741000076325184956930916219694874624

noncomputable def p23050 :=
@p23045 147573952589676412928 773079384532276359667 p23046
  p23047 p23042 p23048 p23042
  p23049 p23041 p23042 p23043

noncomputable def p23051 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  (@Inv.inv Real Real.instInv
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
          (Enclosure.sfrac false 12 1)))))

noncomputable def p23052 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
        (Enclosure.sfrac false 12 1))
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
        (Enclosure.sfrac false 12 1)))
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
      (Enclosure.sfrac false 12 1)))

noncomputable def p23053 :=
@Enclosure.Real.IsNear.of_eq
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
      (Enclosure.sfrac false 12 1)))
  (p23051
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p23052 (Enclosure.sfrac false 1 16)))))

noncomputable def p23054 :=
BSN.cos_two_pi_p_ne_zero_mk
  (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
    true 5)
  102149700 100000 12
  (Enclosure.sfrac_ofScientific_eq 102149700 5 100000 (Eq.refl true))

noncomputable def p23055 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@Inv.inv Real Real.instInv
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
          (Enclosure.sfrac false 12 1)))))

noncomputable def p23056 :=
@p23055
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p23052 (Enclosure.sfrac false 1 16))))
  5053675070673

noncomputable def p23057 :=
@p23056 17179869184 22848931 17179869184 14616477
  8589934592 2161699091 57042534400000000 73866925435965279021
  147573952589676412928 773079384532276359667 p23046

noncomputable def p23058 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv Real Real.instInv
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
          (Enclosure.sfrac false 12 1)))))

noncomputable def p23059 :=
@Enclosure.Real.IsNear.inv_image
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
        (Enclosure.sfrac false 12 1))))
  14600657

noncomputable def p23060 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
        (Enclosure.sfrac false 12 1))))
  false

noncomputable def p23061 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
      (Enclosure.sfrac false 12 1)))
  (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
    (@Nat.cast Real Real.instNatCast 10127078621)
    (@Nat.cast Real Real.instNatCast 2147483648))
  false

noncomputable def p23062 :=
nat_lit 11402076876060929457239015

noncomputable def p23063 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
      (Enclosure.sfrac false 12 1)))
  false p23062

noncomputable def p23064 :=
nat_lit 1106429202531114478096317663

noncomputable def p23065 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
    (Enclosure.sfrac false 12 1))
  884279719003555 140737488355328 1

noncomputable def p23066 :=
@Enclosure.Real.IsNear.subLit_ff_p p22819 (Enclosure.sfrac false 12 1)
  219052627181 17179869184 41 17179869184 12 1 0

noncomputable def p23067 :=
@p23065 500000000000000 12894196973 17179869184 41
  17179869184 p23062 p2602 p23064
  p5018 d260
  (@p23066 1 12894196973 12894196973 17179869184 41
    17179869184 (p23036 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p23068 :=
@p23061 10127078621 2147483648 259 17179869184 false
  58402628 17179869184 1 3400000000
  (@p23063 p2602 p23064 p5018
    10127078621 2147483648 259 17179869184
    (p23067 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div 10127078621 2147483648)

noncomputable def p23069 :=
BSN.cos_reduce3
  (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
    (@Nat.cast Real Real.instNatCast 10127078621)
    (@Nat.cast Real Real.instNatCast 2147483648))
  (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
    (@Nat.cast Real Real.instNatCast 1052090248040169437396992)
    (@Nat.cast Real Real.instNatCast p976))
  226375608064910080 72057594037927936 false

noncomputable def p23070 :=
BSN.sin_reduce_arg_pos_rat_q3 10127078621 2147483648 226375608064910080
  72057594037927936 0 1052090248040169437396992 p976
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p23071 :=
BSN.sin_dyadic_bound_f 119608813297 35184372088832 1 0 17179869184
  6806640626 0 1 1 0 1

noncomputable def p23072 :=
p23071 1 58402628 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (@BSN.binarySplit_of_le (BSN.sinEvenP 119608813297) (BSN.sinEvenQ 35184372088832) 0
    0 (Eq.refl true))

noncomputable def p23073 :=
p23072
  (@BSN.binarySplit_of_le (BSN.sinOddP 119608813297) (BSN.sinOddQ 35184372088832) 0
    0 (Eq.refl true))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p23074 :=
@BSN.sin_arg_round false 58402628 17179869184 1052090248040169437396992
  p976 119608813297 35184372088832 6806640626 6800000000
  p23073 (Eq.refl true)

noncomputable def p23075 :=
p23069 58402628 17179869184 0 1000000000000000
  6800000000 3400000000 p23070 BSN.pi_near_15 p23074
  (Eq.refl true) (Eq.refl true)

noncomputable def p23076 :=
@p23059 4294967296 1753476307 114085068800000000 2526826110871
  2526848959802 8589934592
  (@p23060 58402628 17179869184 897779869184
    58411555225600000000 14600657 4294967296 1753476307
    114085068800000000
    (p23068 (p23075 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p23077 :=
@p23058 false 5053675070673 17179869184 22848931
  17179869184 5053675070673 17179869184 22848931 17179869184
  (p23076 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p23078 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p23052 (Enclosure.sfrac false 1 16))))
  false

noncomputable def p23079 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p23052 (Enclosure.sfrac false 1 16)))
  (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
    (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 26956842439))
    (@Nat.cast Real Real.instNatCast 17179869184))
  true

noncomputable def p23080 :=
nat_lit 65177645681450392283515072730507045

noncomputable def p23081 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p23052 (Enclosure.sfrac false 1 16)))
  true p23080

noncomputable def p23082 :=
nat_lit 9508267405679439700753941374170346937

noncomputable def p23083 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (p23052 (Enclosure.sfrac false 1 16)) 884279719003555
  140737488355328 1

noncomputable def p23084 :=
@Enclosure.Real.IsNear.subLit_tf
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
        (Enclosure.sfrac false 12 1))
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
        (Enclosure.sfrac false 12 1)))
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
      (Enclosure.sfrac false 12 1)))

noncomputable def p23085 :=
@p23084 (Enclosure.sfrac false 1 16) 55260301650346417303
  295147905179352825856 1761698790011 295147905179352825856 1 16
  0

noncomputable def p23086 :=
@Enclosure.Real.IsNear.subLit_ff_n
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
      (Enclosure.sfrac false 12 1))
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
      (Enclosure.sfrac false 12 1)))
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
    (Enclosure.sfrac false 12 1))
  166260315578522362729

noncomputable def p23087 :=
nat_lit 949364753421330757548614090752

noncomputable def p23088 :=
@p23086 295147905179352825856 1057324153467 295147905179352825856
  12894196973 17179869184 41 17179869184 p23087
  55260301650346417303 295147905179352825856 1761698790011

noncomputable def p23089 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
    (Enclosure.sfrac false 12 1))
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
    (Enclosure.sfrac false 12 1))
  12894196973 17179869184 41

noncomputable def p23090 :=
@p23089 17179869184 12894196973 17179869184 41
  17179869184 166260315578522362729 295147905179352825856 1057324153467
  295147905179352825856
  (@p23066 1 12894196973 12894196973 17179869184 41
    17179869184 (p23036 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p23091 :=
p23090
  (@p23066 1 12894196973 12894196973 17179869184 41
    17179869184 (p23036 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p23092 :=
@p23088 295147905179352825856 (p23091 (Eq.refl true))
  (@p23066 1 12894196973 12894196973 17179869184 41
    17179869184 (p23036 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p23093 :=
@p23083 500000000000000 73707045724055968919 295147905179352825856
  1761698790011 295147905179352825856 p23080 p2630
  p23082 p10041 d260
  (@p23085 1 1179312731584895502704 73707045724055968919
    295147905179352825856 1761698790011 295147905179352825856
    (p23092 (Eq.refl true) (Eq.refl true))
    (Enclosure.Real.IsNear.const false 1 16) (Eq.refl true)
    (Eq.refl true))

noncomputable def p23094 :=
@p23079 26956842439 17179869184 323 8589934592 false
  14616477 8589934592 1 3400000000
  (@p23081 p2630 p23082 p10041
    26956842439 17179869184 323 8589934592
    (p23093 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_true_div 26956842439 17179869184)

noncomputable def p23095 :=
nat_lit
  80264889115643470683029115239397787648779625492192275348678873309854261776307724958482792339999082061931805966940667458030673664801

noncomputable def p23096 :=
nat_lit
  316646866740079143295725755612190180511469568587383446887297628374512813051459112748418952103360324986451946705925428665111910809600

noncomputable def p23097 :=
nat_lit
  147240825167204418684137356226339514618559416429711103741085691138991021902511799904727206431665515089653633734846227443948321

noncomputable def p23098 :=
nat_lit
  485772484458187281860654482742053134195809977069584095549355624375180070083963700081151021866422980390699076832362055005331911154465

noncomputable def p23099 :=
nat_lit
  28814864873347202039911043760709306426543730741451893666744084182080665987682779260106124641405789573767127150239214008525183883673600

noncomputable def p23100 :=
BSN.cos_dyadic_bound_f 26956842439 17179869184 4 3 8589934592
  3400000000 p23095 p23096 p23097
  p23098 p23099

noncomputable def p23101 :=
@BSN.binarySplit_of_base3 (BSN.cosEvenP 26956842439) (BSN.cosEvenQ 17179869184) 0
  3 p23095 p23096 p23097 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p23102 :=
p23100 p23097 14616477 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p23101 (Eq.refl true))

noncomputable def p23103 :=
@BSN.binarySplit_of_base3 (BSN.cosOddP 26956842439) (BSN.cosOddQ 17179869184) 0
  3 p23098 p23099 p23097 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p23104 :=
p23094
  (BSN.cos_neg_of_bound 26956842439 17179869184 false 14616477 8589934592
    1 3400000000
    (p23102 (p23103 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p23105 :=
p23057 p23077
  (@p23078 14616477 8589934592 1106789934592
    29205777612800000000 14616477 8589934592 2161699091
    57042534400000000 (p23104 (Eq.refl true)) (Eq.refl true))

noncomputable def p23106 :=
@p23050 p23044
  (@p23053 false 73866925435965279021 147573952589676412928
    773079384532276359667 p23046
    (BSN.correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
        (Enclosure.sfrac false 12 1))
      (p23054 (Eq.refl true) (Eq.refl true)
        (p22822 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p23105 (Eq.refl true)))

noncomputable def p23107 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Zeta.RiemannSiegel.correctionLinear
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
        (Enclosure.sfrac false 12 1)))
    (@Inv.inv Real Real.instInv p22819))
  true

noncomputable def p23108 :=
nat_lit
  20192043423249398628383374254889060693463314564563915021354803804180880585314198581016685646822295218949006839305325466466868765877253626300841824181175643869027138535279921879798520752065111422507222783581655600562264568371186853937109161561067812703884518663563915483493866723030333657956196484737436025729988963299

noncomputable def p23109 :=
nat_lit
  24707306311927565716857342128774085333197833223161879682238935306082805123046306993647507776054336486228891340858985829027076261887914242781617846672453431386903982455635542158748401823985988322905245077938567513252198179128990807936780194781391547404884040101606295111368825026273254703636026307207764436438929167613952

noncomputable def p23110 :=
nat_lit
  60676228900020376890939832695937098740504353600060567302875650250952649046245049180641655013639797294830530613733023584164492772083486063760754045922342422875960364446732409772651973961243039882045478346410846244989035153994195187803426279530269839093603308878711668817855665933173769875228773147138431938902427

noncomputable def p23111 :=
nat_lit
  119888912184899884028171709687373534931421514018811053677851976521873748431733547020471466567487157726183462067310660083091344424953158705348367081919329980292691706113221889726737055960749429621991718691091008904661311899597828865495535020790295848849313354318739790002920604011950638209404739381245915087293

noncomputable def p23112 :=
@Enclosure.Real.IsNear.mulLit_tf
  (Zeta.RiemannSiegel.correctionLinear
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
      (Enclosure.sfrac false 12 1)))
  (@Inv.inv Real Real.instInv p22819) p23111 p22472

noncomputable def p23113 :=
nat_lit
  44943654067626173169040362458344674787629425367824520137933908148252520888223252530071480884086965195212757297294257535843028194184681623724834828018912955387736101046775873187726486386291591579539362007111637413512227825657741377033210961082553952491827442521249943353436754325009264464492257060527579

noncomputable def p23114 :=
nat_lit
  5752618031559410904733776610524879147577526332615381032749762597047445625776030820246671274317041152675843644155884587445081272602061331919771117780463171980088572589595695528841671027239875011822498654466720184602820821834958812207165219537306471589227216341906761543678311870031350921754731402547975172390912

noncomputable def p23115 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  (@iteratedDeriv Real (@DenselyNormedField.toNontriviallyNormedField Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal Real Real.instRCLike))
    (@OfNat.ofNat Nat 3 (instOfNatNat 3)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
      (Enclosure.sfrac false 12 1)))
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 96 1)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) Real.pi Real.pi)))

noncomputable def p23116 :=
@Enclosure.Real.IsNear.of_eq
  (Zeta.RiemannSiegel.correctionLinear
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
      (Enclosure.sfrac false 12 1)))
  (@Neg.neg Real Real.instNeg p23115) true p23111

noncomputable def p23117 :=
nat_lit
  552890020087571696794085413553059066141854255424352949847003709202998084271815857790715709884799723868485355406160901739954481231147607840712862088077026871008120626028565328578245011873900984495409639394832219887883076881920861124821936018582781310115980751392021051278220675456775853963569966923205562679501364808867022282705

noncomputable def p23118 :=
nat_lit
  53058536290991634737396540170283858539198978395771271474551549598742698935712572215646062825029533563666321339663466341699370021653261445199826360714064955944866263669556212233526813063143284104557957658305559283253118889734882642786544086063293282737405311454375777285526890640894984855797452638426498665888535738081213096656896

noncomputable def p23119 :=
nat_lit
  414532042161417646729148028866114884690679916402434863668696372633899571214964561441095454233176166544082616743324655770179449130762883693677707847610658691627768052465722995782186145750801002600499816613681064077393402287570639781404929638746107954968190361332689478870347601835780636557783687350715685871941722330894431

noncomputable def p23120 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@iteratedDeriv Real (@DenselyNormedField.toNontriviallyNormedField Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal Real Real.instRCLike))
    (@OfNat.ofNat Nat 3 (instOfNatNat 3)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
      (Enclosure.sfrac false 12 1)))
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 96 1)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) Real.pi Real.pi)))

noncomputable def p23121 :=
nat_lit
  443721050753213823362715825209535901758432340173415746582654495733524680957375669285441383539121832175838049691581530920072645099866483062532574994202800861050860518945801731031120532770310916597659724674197191780613743287395667567756410487063204803225369293519752043888042825387504830036238347789356170473055

noncomputable def p23122 :=
nat_lit
  10396314515306393500686143497223683193305224758712801681188522661372261629469447302964375990033646497222145227696323748004673999292493020621125022648233243989333685168521143573795246938277087004581981123144333744778151356233792241096102158628974780302990848257655353454030867391767962131447790017258149

noncomputable def p23123 :=
nat_lit
  1404447761611184302913519680303925573139044514798677009948672509044786529730476274474284979081308875165000889686495260606709295068862629863225370551870891596701311667381761603721111090634735110308227210563164107569048052205800491261514946176100212790338675864723330454999587858894372783631526221325189251072

noncomputable def p23124 :=
@p23120 p23121 p20904 p23122
  p23123 1246030629263687631 1180591620717411303424 1
  1180591620717411303424 p23117 p23118 p23119

noncomputable def p23125 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p23126 :=
p23125
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p23127 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p23126
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p23128 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p23127
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p23052 (Enclosure.sfrac false 1 16)))))

noncomputable def p23129 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  (Enclosure.sfrac false 3 1)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p23130 :=
p23128
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p23129
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 4 1) Real.pi))
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p23052 (Enclosure.sfrac false 1 16)))))

noncomputable def p23131 :=
@Neg.neg Real Real.instNeg
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
          (Enclosure.sfrac false 12 1)))))

noncomputable def p23132 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p23130
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 3 1) p23131)
    (@iteratedDeriv Real (@DenselyNormedField.toNontriviallyNormedField Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal Real Real.instRCLike))
      (@OfNat.ofNat Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
        (Enclosure.sfrac false 12 1))))

noncomputable def p23133 :=
@Neg.neg Real Real.instNeg
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 4 1)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) Real.pi Real.pi))
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
          (Enclosure.sfrac false 12 1)))))

noncomputable def p23134 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p23132
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 3 1) p23133)
    (@iteratedDeriv Real (@DenselyNormedField.toNontriviallyNormedField Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal Real Real.instRCLike))
      (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
        (Enclosure.sfrac false 12 1))))

noncomputable def p23135 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 8 1)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) Real.pi Real.pi) Real.pi))
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
        (Enclosure.sfrac false 12 1))))

noncomputable def p23136 :=
@Enclosure.Real.IsNear.of_eq
  (@iteratedDeriv Real (@DenselyNormedField.toNontriviallyNormedField Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal Real Real.instRCLike))
    (@OfNat.ofNat Nat 3 (instOfNatNat 3)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
      (Enclosure.sfrac false 12 1)))
  (p23051
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p23134
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p23135
        (Zeta.RiemannSiegel.correction
          (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
            (Enclosure.sfrac false 12 1))))))

noncomputable def p23137 :=
@Enclosure.Real.IsNear.recentre'
  (p23051
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p23134
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p23135
        (Zeta.RiemannSiegel.correction
          (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
            (Enclosure.sfrac false 12 1))))))

noncomputable def p23138 :=
nat_lit
  60984556849017905223615526880531489452490745384754163205885594241371521136664399026146637799216672184154398234168497978218393620740518359043690641112589417274050755888953818600923233487442613329239427443585318200088833095280125478899252708361212662873698445862078712272905619855576696705525830355723476770482339880413863

noncomputable def p23139 :=
nat_lit
  6176826577981891429214335532193521333299458305790469920559733826520701280761576748411876944013584121557222835214746457256769065471978560695404461668113357846725995613908885539687100455996497080726311269484641878313049544782247701984195048695347886851221010025401573777842206256568313675909006576801941109109732291903488

noncomputable def p23140 :=
nat_lit
  49095207212454093786257343291950648352920530949375997985402033795089865296652840495951047086269923882846666805716251699121402917222885128521670673812154352906212999659320170104230123347760303168422795127253597629549776701530441595407664250001804091539699449358688868920139295086720872476488609289523433329416240876834426445

noncomputable def p23141 :=
nat_lit
  6632317036373954342174567521285482317399872299471408934318943699842837366964071526955757853128691695458290167457933292712421252706657680649978295089258119493108282958694526529190851632892910513069744707288194910406639861216860330348318010757911660342175663931796972160690861330111873106974681579803312333236066967260151637082112

noncomputable def p23142 :=
@p23055
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p23134
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p23135
      (Zeta.RiemannSiegel.correction
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
          (Enclosure.sfrac false 12 1)))))
  347286923913144613691821

noncomputable def p23143 :=
nat_lit
  175602801746344916821840618910308237691271344392941114700108150566566936401654784778490096745551306597471836504974535343833218755067042551146139900414500625149422602658626486581702602410832679110888023752784998382572281866038079538570630579158275432814891628133834822390545260152685822850196410403

noncomputable def p23144 :=
nat_lit
  5231975621026695903068481684863290090631859432155925817596437443214604741820977160611320209061014932263645863855239974732359107840294502166008094518895788478483675671300894035850134084503110909120094815504417224113077119759472054472248800754920440876255467030120381917802944253736633001385354330112

noncomputable def p23145 :=
nat_lit
  282735708301095791191669570398908746767658087775095862321688805267017629876797843418108959304304470688527592914426802221694705793529485109572931087007346914249301077345684512996798284529218134563186533550668016127484338323841303695778131883736889291579878445836514980257778072355072963552479471730855

noncomputable def p23146 :=
nat_lit
  11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576

noncomputable def p23147 :=
@p23142 1180591620717411303424 22849065 1180591620717411303424
  p23143 p23144 p23145 p23146
  p23138 p23139 p23140 p23141

noncomputable def p23148 :=
@Enclosure.Real.IsNear.inv_image
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
        (Enclosure.sfrac false 12 1))))
  2006693138922714179

noncomputable def p23149 :=
nat_lit 7839866231326559436800000000

noncomputable def p23150 :=
nat_lit 275840770609662717765682617489817600000000

noncomputable def p23151 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
      (Enclosure.sfrac false 12 1)))
  (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
    (@Nat.cast Real Real.instNatCast 2783710168905582433017)
    (@Nat.cast Real Real.instNatCast 590295810358705651712))
  false

noncomputable def p23152 :=
nat_lit 4166038496983237675640132258283581861105820680089250805306358638556422419

noncomputable def p23153 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
      (Enclosure.sfrac false 12 1)))
  false p23152

noncomputable def p23154 :=
nat_lit 17121160916665483071190193476421764569421079186691803745031054353840010064193307589157093

noncomputable def p23155 :=
nat_lit 78463771692333509547947367790095830201279443055800431411200000000000000000000000000000000000000000000000000

noncomputable def p23156 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
    (Enclosure.sfrac false 12 1))
  p20538 p20539 1

noncomputable def p23157 :=
@Enclosure.Real.IsNear.subLit_ff_p p22819 (Enclosure.sfrac false 12 1)
  15053181915641932291415 1180591620717411303424 41 1180591620717411303424
  12 1 0

noncomputable def p23158 :=
nat_lit 38387242770317496407681403

noncomputable def p23159 :=
@p23030
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 102149700 100000)
    (@Inv.inv Real Real.instInv
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)))
  false p23158

noncomputable def p23160 :=
@p23159 236118324143482260684800 1021497 1180591620717411303424000
  (BSN.t_div_two_pi_mk
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
      true 5)
    102149700 100000
    (Enclosure.sfrac_ofScientific_eq 102149700 5 100000 (Eq.refl true)))

noncomputable def p23161 :=
@p23033 1 187896992210048078495 1180591620717411303424 1
  1180591620717411303424 p23158 236118324143482260684800 1021497
  1180591620717411303424000 (Enclosure.Real.IsNear.const false 102149700 100000)
  d283

noncomputable def p23162 :=
@p23029 p23158 236118324143482260684800 1021497
  1180591620717411303424000 7526590957820966145687 7526590957820966145728
  590295810358705651712 (p23160 (p23161 (Eq.refl true)))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p23163 :=
@Enclosure.Real.IsNear.recentre' p22819 false 15053181915641932291415
  1180591620717411303424 41 1180591620717411303424 15053181915641932291415
  1180591620717411303424 41 1180591620717411303424
  (p23162 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p23164 :=
@p23156 p20541 886082467032996650327 1180591620717411303424
  41 1180591620717411303424 p23152 p18792
  p23154 p23155 d282
  (@p23157 1 886082467032996650327 886082467032996650327
    1180591620717411303424 41 1180591620717411303424
    (p23163 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p23165 :=
@p23151 2783710168905582433017 590295810358705651712 259
  1180591620717411303424 false 4013386277845428358 1180591620717411303424 1
  233646220902400000000
  (@p23153 p18792 p23154 p23155
    2783710168905582433017 590295810358705651712 259 1180591620717411303424
    (p23164 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div 2783710168905582433017 590295810358705651712)

noncomputable def p23166 :=
nat_lit 24025423519130993719329333818986782117151842656617773677215344802922496

noncomputable def p23167 :=
nat_lit 7067388259113537318333190002971674063309935587502475832486424805170479104

noncomputable def p23168 :=
BSN.cos_reduce3
  (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
    (@Nat.cast Real Real.instNatCast 2783710168905582433017)
    (@Nat.cast Real Real.instNatCast 590295810358705651712))
  (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
    (@Nat.cast Real Real.instNatCast p23166)
    (@Nat.cast Real Real.instNatCast p23167))
  p2138 p2102 false

noncomputable def p23169 :=
BSN.sin_reduce_arg_pos_rat_q3 2783710168905582433017 590295810358705651712 p2138
  p2102 0 p23166 p23167 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p23170 :=
nat_lit 4564224532163143604682457234609675477821889523710296432863644602861320884647693733779601

noncomputable def p23171 :=
nat_lit 4101095108968147358198441675845540060037192682924773318298319887018661873498829856044087206918225920

noncomputable def p23172 :=
nat_lit 28707665762777031507389091730918780420260348780473413228088239209130633114491808992308610448427581440

noncomputable def p23173 :=
BSN.sin_dyadic_bound_f 8219430928249903273651 p2602 2 1
  1180591620717411303424 467748782080000000001 p23170 p23171
  p23170 p23170 p23172

noncomputable def p23174 :=
@BSN.binarySplit_of_base (BSN.sinEvenP 8219430928249903273651) (BSN.sinEvenQ p2602)
  0 1 p23170 p23171 p23170
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p23175 :=
p23173 p23170 4013386277845428358 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p23174 (Eq.refl true))

noncomputable def p23176 :=
@BSN.binarySplit_of_base (BSN.sinOddP 8219430928249903273651) (BSN.sinOddQ p2602)
  0 1 p23170 p23172 p23170
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p23177 :=
@BSN.sin_arg_round false 4013386277845428358 1180591620717411303424 p23166
  p23167 8219430928249903273651 p2602 467748782080000000001
  467292441804800000000
  (p23175 (p23176 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p23178 :=
p23168 4013386277845428358 1180591620717411303424 0
  p2139 467292441804800000000 233646220902400000000 p23169
  d102 p23177 (Eq.refl true) (Eq.refl true)

noncomputable def p23179 :=
@p23148 590295810358705651712 1753476307 p23149
  173643461956572295421378 173643461956572318270443 590295810358705651712
  (@p23060 4013386277845428358 1180591620717411303424
    61694962834439011303424 p23150 2006693138922714179
    590295810358705651712 1753476307 p23149
    (p23165 (p23178 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p23180 :=
@p23058 false 347286923913144613691821 1180591620717411303424
  22849065 1180591620717411303424 347286923913144613691821
  1180591620717411303424 22849065 1180591620717411303424
  (p23179 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p23181 :=
nat_lit
  649420078505454496672839287044893747938633192523248951449732228960455530760914518439814189246821273815579677269110464007566660085368852189188986811122998346734559106604368677884825766907158853199347744358131725929839013777909806118804938983078049622080644179393733421742967281433259538929295285186525

noncomputable def p23182 :=
@Enclosure.Real.IsNear.subLit_tt_p p23134
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p23135
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
        (Enclosure.sfrac false 12 1))))
  p23181 p23144

noncomputable def p23183 :=
nat_lit
  4523762636781358195202572925488269613697034625406593769755378270851364248826152242060454657730891810958590355856087505297440529166121652183927811390576400635709616564910566435914871334240619099675090979586353946237000444105055182127756214255753687695203080472769922926367754008419112711439378450326265

noncomputable def p23184 :=
nat_lit
  2675064943518829357137593383149975249568907831048497400832144641888131072143373388993795651557871715167737844070013701835656697607383909654673059127486207385045043137479979676866832525890125560304674903226540547718599

noncomputable def p23185 :=
nat_lit
  21545516652742137885659094560277007014094191832363720128504958578969526904000843047377578132593002296225722240434905979752527594496752860623371529300590103961416596156942109074193054752294185849943217159109760516096

noncomputable def p23186 :=
nat_lit
  8696036174463864140200894270334585494778994940027391642613420917829202613252629288691137979720057851130774741330249674763530350109569239086001541149992279200672620385772033901218226871053335893557224334311802748969076405677004693895884036540970074974660614316757756695149262054705400293097367415

noncomputable def p23187 :=
nat_lit
  3783453089294050577524367546473111590694504927485222044365614516760374041225824609344992883459168616772893936862326285972023559522061258401885690546014094971083837699523752066980250737255450715676769637136489983128145885690958656057449908992819850720521327999094026695659088643083736721063489470940418555474502473579245031131520604336529220770391627922535136551319692963389096940536039318734760802995467957127503365592669070336215635265072641086261026230854234474857758616424988140703907635895692777799903346688

noncomputable def p23188 :=
@p23182 p23183 p20578 p23184
  p23185 p23186 p20578 p23187
  p23143 p23144 p23145 p23146

noncomputable def p23189 :=
nat_lit
  18095050547125432780810291701953078454788138501626375079021513083405456995304608968241818630923567243834361423424350021189762116664486608735711245562305602542838466259642265743659485336962476398700363918345415784948001776420220728511024857023014750780812321891079691705471016033676450845757513801305059

noncomputable def p23190 :=
@Enclosure.Real.IsNear.subLit_tt_n p23132
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 3 1) p23133)
    (@iteratedDeriv Real (@DenselyNormedField.toNontriviallyNormedField Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal Real Real.instRCLike))
      (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
        (Enclosure.sfrac false 12 1))))

noncomputable def p23191 :=
nat_lit
  651532188784397330947121365699194475138308560204490022258573686071690997304792968351006151441837793874421505228320813899865624246037124263724855106015740385708460104373726375531154514039853744278066908780007720453838162455443180150223065839932269713779385807369398563323153264978977628922250567774173

noncomputable def p23192 :=
nat_lit
  1130934123230666803060185666664384755345258801496631997473694362638149857180852278099307141055513774423614107424431334645715414040724100370772735376190095469246355802185718326121977186449104319411734074884894909598388385513170811857961471264116665243818710816043528976457593168297859173180340710533083

noncomputable def p23193 :=
nat_lit
  6061459231472137598222631721568030693205386627368028347021036370635157207902606506336121456496743601214562348843522729310152648518859991454773801668220327740238452271947134937752589048937743247879666405947089549303611162054386569407723515826422760672023917

noncomputable def p23194 :=
nat_lit
  15015033657609400459942315391018513722623519187099007073355798781525263125238463415894820397160662761697108038369410925238365381332604486523522921813279810320079453845181805154673256699778290824639959535835805252308660678089369234238529227774479195332149248

noncomputable def p23195 :=
nat_lit
  104575434763931847321035322922369263997677680263119442403281195059280410972518652904374035346853056535704633448666858315492012901002803347479543264075034896773424670772525707850353776807288112618720187097231373787608209487738783641316797148106879712948834383228082149525340910704074872062432775731

noncomputable def p23196 :=
nat_lit
  9751064336686738420161674952219147162510411551236392634699528679971042262865916666121619706754716260828279785010640477954345626520880064949737166140628372816284771291417210886585047920921710781195912580656688435054817860530439548236246846583959984097004184559090927254875711157494547991825791164516180022654218306437571057548586540803858042398065075423487980254484931473626307906866156722238272395123496824406496590087617922240250778394166188254658852118600868397583235072918602274921740936006013299726284918341761652225224154829651498922460992024818483200

noncomputable def p23197 :=
@p23190 p23191 p23144 p23192
  p20904 p23193 p23194 p23195
  p22175 p23196 p23181 p23144

noncomputable def p23198 :=
@Enclosure.Real.IsNear.subLit_tf p23130
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 3 1) p23131)
    (@iteratedDeriv Real (@DenselyNormedField.toNontriviallyNormedField Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal Real Real.instRCLike))
      (@OfNat.ofNat Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
        (Enclosure.sfrac false 12 1))))

noncomputable def p23199 :=
nat_lit
  1597915103109622812886596022845898405264349770258618164343533959494718766111083925413732462952722449435470754860034654243690956594945528474394929921002429251746625130542509856853138874221480314778465369075501281054349949530128771408799835

noncomputable def p23200 :=
nat_lit
  50872912848509630386961759877939283730657641008879914553804457182037637617627197811290223700497087789481581959483591006819830334885554237978846405428549423569451580654251209705071092879576217840034217957579701248029256805705844583825408

noncomputable def p23201 :=
nat_lit
  8587820432459167385368898521522663539668619739685031889001784316105595399374590659598470048242878485910689445818086089665009503443237328722943266473465032099683253403221355053004506647654609776343538282567392478576998070607520943637272660601511300850646594125052341465610350730850109986954839

noncomputable def p23202 :=
nat_lit
  487196152260693006251774896138184804435055028467486060697834106154569394238865584586037338487022732684502946526115082485070111984055186330197392939074441773161763636757871242194797635004354615306064015781495078750322229632731302814682762421125559226387483403405172920782931847336762563368286787104733

noncomputable def p23203 :=
nat_lit
  2261868237873513173661203947959870989167854063324644255262356836274515398256109156824023622512557500604349728938173223473344738416438697298308142029436924465027679504688183249022599319893701991168858373426251536629384292449343553108401998890960669886126120781440463827862844870985367615510571434111327

noncomputable def p23204 :=
nat_lit
  33145340258027369080964953334600604666160180684612081452694889213809447878659295789570069260999610975287130749817575608187013375625118210113392558552880321134451859406051479951119334222750194439623806360928159339066629886497335684425241062423257027041276954357931507187959239287080094871917074632741824692672374313955174714432744161741603933301132028164782602076282382765793079675287543214994063029138766063391633357690568884567390162884150884187754071541773837956073777169544433774098508805345804040310573683134921662796376000203587584

noncomputable def p23205 :=
@p23198 p23199 p23200 p23201
  p20924 p23202 p23144 p23203
  p20924 p23204 p23191 p23144

noncomputable def p23206 :=
nat_lit
  449875502358707334286984876877375259121962659050849523015257270806121290720979496015443672404125530829811486776684635034614433739368179100957364516659387955349674071462305386901562219768596777255261101483546388288667314246337919500628332164570720167644847620419567384735297109857997498200253528130425044862294414934850886101809214896375594467964448696419680052127392053

noncomputable def p23207 :=
nat_lit
  4708634213380946231552783859623281196175408256838043370088212491641005719402222773110095662332076199357691836437821489173495760033701247914218179858986420303268452042267996418667150468972150520755735473390663868282577344778352223615845792365433124343157702459529125414416941056000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p23208 :=
@Enclosure.Real.IsNear.subLit_tf
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p23127
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p23052 (Enclosure.sfrac false 1 16)))))

noncomputable def p23209 :=
@p23208
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p23129
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 4 1) Real.pi))
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p23052 (Enclosure.sfrac false 1 16)))))

noncomputable def p23210 :=
nat_lit
  1587640665570879611531247093949955146855796341486340009191045969548056090213937420538734366919133778603401271293529241585402036927213663243840188084396544872998225092132062777732425170022389831724551541891611174929449500798472030783350875

noncomputable def p23211 :=
nat_lit
  2711026960694272321957506474919654921486550164633099771243727166554292392764693443774834062455382242105480150353378053381374679750596619332978415592056347750812213005419901463270978203965986110587109186253884758592762030002823778752019352577804418978680648640298891822943814030774822981080533

noncomputable def p23212 :=
nat_lit
  2462801473684272800787616694287475300996927550339021509012495812054292076018267274035571895104678754379744588874692841383542755573962822951645

noncomputable def p23213 :=
nat_lit
  41765934915790444718467895395312569644209695178458767471730072900086107479367741341251548888111215040295784907601526672810163624640206278966336038147456622005291743753653278586967511854519774313737194411

noncomputable def p23214 :=
nat_lit
  638803582514482637985938722326699671446185653303063004832383144256760854831173496622126127560657087224686313472000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p23215 :=
nat_lit
  19485504518205055727209442092807714903133433658601762462038955183861002925429194363255353413310989487898306104446800405162512141216168327988841576313291435351090678520769991633401385051244535982768905318705198655794376428692906253531142550384692000649378892736292033254371781844377279646115350681490824038066475297456528244066253637740692413935849833105937491011943448820485980160

noncomputable def p23216 :=
@p23209 p23210 p23200 p23211
  p20924 p23212 p7287 p23213
  p23214 p23215 p23199 p23200

noncomputable def p23217 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p23127
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p23052 (Enclosure.sfrac false 1 16)))))

noncomputable def p23218 :=
nat_lit
  42508177442725802658933104272261445290234953585611050883930107647163739874357876758642362839592516923057411641813876323148266348449687978081028843050815711286167462077881376957714374385934462618158233687703338809320314057232606613511837361864237822228084730900969063152907861055160373364619570165340678119131652972776403

noncomputable def p23219 :=
nat_lit
  1409367370229465297712095598273164992447472863637674398542775536216602940479865199478098543789846985284886660584810824701389516200164757138120387706467350392285510128722586887453055971989743484027320750298741418461410970508582820199017577286056227822712328585506856584146808032648773035232119835708203870812664230542782222879948800000000

noncomputable def p23220 :=
nat_lit
  2689571797926086950812990761106183812938841386082525118674576455320775335155617126182221530845086293649515455656793954302543036722019981570771259406272025380552682472987578220898481872672795352553560748689861266748875

noncomputable def p23221 :=
@Enclosure.Real.IsNear.mulLit_ft p23127
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p23052 (Enclosure.sfrac false 1 16))))
  p23220

noncomputable def p23222 :=
nat_lit
  86182066610968551542636378241108028056376767329454880514019834315878107616003372189510312530372009184902888961739623919010110377987011442493486117202360415845666384627768436296772219009176743399772868636439042064384

noncomputable def p23223 :=
nat_lit
  2332965578025709516024178576302606651046112922127613097383951908249194900520223733543504361630703667632578811146344120862944806267681673862409414188661542761435324734712502851213497476020626720838887363832059601393561897754219994708964579890855437547008519882118817863127067582250712434545029

noncomputable def p23224 :=
@p23221 p23222 p23223 p20578
  590294955797461894577 590295810358705651712 4316757557 p23149
  p23210 p23200 p23218 p23219

noncomputable def p23225 :=
nat_lit
  783628685819767836351762551989961796428580129302428507520109515074010700699310793400488197163082820068669297885560918934013018830625927650417108772530406492925999916384269960077535601319753449170016342074732068357785482037952341786036980449295264359812259218497899835701518927469624756886331176141962141

noncomputable def p23226 :=
nat_lit
  60383398797144661635864873295812302254670739526663046854019300803929986598274381633378027602842540280663494000492221518396329354078796682120982948022923136698390325231616000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p23227 :=
@Enclosure.Real.IsNear.mulLit_ff p23126
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p23228 :=
nat_lit
  1933995361588980193286169158960903429647076475796419613542888402365607308512792108268951840708730724658325756558968045012403670771614562786994025

noncomputable def p23229 :=
nat_lit
  195109284394749514461349826862072894109287383916560696928697309976585733676235351257519131441468248197489183195087913930965498479955517831643136

noncomputable def p23230 :=
nat_lit
  4229520513223745890076060052211118894509518905080638517360856513667524418061267877251577432064613948779359560403583423420288454103345991649819874402524781587344848191722668397561930558533530435111

noncomputable def p23231 :=
nat_lit
  1539140867046659344229650003911859914260927315252556510466730211103348506699109789508369775581442017219008905871360000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p23232 :=
nat_lit 1390681617621006808023593693390012962688207632845046742840036177496187155

noncomputable def p23233 :=
nat_lit 17121160916665483071190193476420979931704155851596324271353153395537997269762749584842981

noncomputable def p23234 :=
nat_lit 39231885846166754773973683895047915100639721527900215705600000000000000000000000000000000000000000000000000

noncomputable def p23235 :=
@p23227 p23228 p23229 p23230
  p23231 p23232 p18799 p23233
  p23234 p23220 p23222 p23225

noncomputable def p23236 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p23237 :=
@p23236
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p23238 :=
@p23237 p23232 p18799 p23233
  p23234 p23232 p18799 p23233
  p23234 p23228 p23229 p23230

noncomputable def p23239 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
        (Enclosure.sfrac false 12 1)))
    (Enclosure.sfrac false 1 1))
  p20538

noncomputable def p23240 :=
@p23239 p20539 1 p20541 295786656674290998615
  590295810358705651712 41 590295810358705651712 p23232
  p18799 p23233 p23234

noncomputable def p23241 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
      (Enclosure.sfrac false 12 1)))
  (Enclosure.sfrac false 1 1) 886082467032996650327 590295810358705651712

noncomputable def p23242 :=
@p23241 41 590295810358705651712 1 1 0 1
  295786656674290998615 295786656674290998615 590295810358705651712 41
  590295810358705651712

noncomputable def p23243 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 2 1)
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
    (Enclosure.sfrac false 12 1))
  2 1 0 1

noncomputable def p23244 :=
@p23243 886082467032996650327 1180591620717411303424 41
  1180591620717411303424 886082467032996650327 590295810358705651712 41
  590295810358705651712 (Enclosure.Real.IsNear.const false 2 1)
  (@p23157 1 886082467032996650327 886082467032996650327
    1180591620717411303424 41 1180591620717411303424
    (p23163 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p23245 :=
@p23238 p23231
  (p23240 d282
    (p23242 (p23244 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (p23240 d282
    (p23242 (p23244 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))

noncomputable def p23246 :=
@p23235 p23226 (p23245 (Eq.refl true))
  (p23240 d282
    (p23242 (p23244 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p23247 :=
@Enclosure.Real.IsNear.recentre' p23127 false p23220 p23222
  p23225 p23226 p23220 p23222
  p23223 p20578 p23246

noncomputable def p23248 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p23052 (Enclosure.sfrac false 1 16))))
  true

noncomputable def p23249 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p23052 (Enclosure.sfrac false 1 16)))
  (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
    (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 1852460112842789150575))
    (@Nat.cast Real Real.instNatCast 1180591620717411303424))
  true

noncomputable def p23250 :=
nat_lit 1636506856497658313639923725953886774362786137885823496273620512746475741345763983976569674635

noncomputable def p23251 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p23052 (Enclosure.sfrac false 1 16)))
  true p23250

noncomputable def p23252 :=
nat_lit 1042962419883256876169444192465601618458351817556959360325703910069443225478828393565899456512

noncomputable def p23253 :=
nat_lit 50554620122185449254010910282967044508510497226243902393782518108625941236790882009280477618864445940409074259

noncomputable def p23254 :=
nat_lit
  92633671389852956338856788006950326282615987732512451231566067206330503711948800000000000000000000000000000000000000000000000000

noncomputable def p23255 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (p23052 (Enclosure.sfrac false 1 16)) p20538
  p20539 1

noncomputable def p23256 :=
nat_lit 348071683392246337475988183819449378745455

noncomputable def p23257 :=
nat_lit 260959397460486090829364284316916716612719

noncomputable def p23258 :=
@p23084 (Enclosure.sfrac false 1 16) p23257
  p12450 121063018746119588768879 p12450 1 16
  0

noncomputable def p23259 :=
nat_lit 5569146934275941399615810941111190059927280

noncomputable def p23260 :=
nat_lit 785142138383281595650057812350802309206929

noncomputable def p23261 :=
@Enclosure.Real.IsNear.subLit_ff_n
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
      (Enclosure.sfrac false 12 1))
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
      (Enclosure.sfrac false 12 1)))
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
    (Enclosure.sfrac false 12 1))
  p23260

noncomputable def p23262 :=
nat_lit 308086477989314381432575325950365984256002979972765172006649856

noncomputable def p23263 :=
@p23261 p12450 72658762296705725328495 p12450
  886082467032996650327 1180591620717411303424 41 1180591620717411303424
  p23262 p23257 p12450 121063018746119588768879

noncomputable def p23264 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
    (Enclosure.sfrac false 12 1))
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
    (Enclosure.sfrac false 12 1))
  886082467032996650327 1180591620717411303424 41

noncomputable def p23265 :=
@p23264 1180591620717411303424 886082467032996650327
  1180591620717411303424 41 1180591620717411303424 p23260
  p12450 72658762296705725328495 p12450
  (@p23157 1 886082467032996650327 886082467032996650327
    1180591620717411303424 41 1180591620717411303424
    (p23163 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p23266 :=
p23265
  (@p23157 1 886082467032996650327 886082467032996650327
    1180591620717411303424 41 1180591620717411303424
    (p23163 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p23267 :=
@p23263 p12450 (p23266 (Eq.refl true))
  (@p23157 1 886082467032996650327 886082467032996650327
    1180591620717411303424 41 1180591620717411303424
    (p23163 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p23268 :=
@p23255 p20541 p23256 p12450
  121063018746119588768879 p12450 p23250 p23252
  p23253 p23254 d282
  (@p23258 1 p23259 p23256 p12450
    121063018746119588768879 p12450
    (p23267 (Eq.refl true) (Eq.refl true))
    (Enclosure.Real.IsNear.const false 1 16) (Eq.refl true)
    (Eq.refl true))

noncomputable def p23269 :=
@p23249 1852460112842789150575 1180591620717411303424 645
  1180591620717411303424 true 590294955797461894577 590295810358705651712 1
  233646220902400000000
  (@p23251 p23252 p23253 p23254
    1852460112842789150575 1180591620717411303424 645 1180591620717411303424
    (p23268 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_true_div 1852460112842789150575 1180591620717411303424)

noncomputable def p23270 :=
nat_lit
  42201104832829365775626750328262030410336046464239018795143532228417652353227638558415940459435507833262454573130668737159631631998042658088812648227213511610338182059536762219432205675350123928674495903027834369042223608137848650954030967947568315812102087360989537373632589125430793110217159423130478774242369019426871929831643877862274171834478171138921139547572391409533249485761182930324475564207077649352393732181435139543384696167572910767770168078599180712635651676587941062019045535629028066814863878442548338511962890625

noncomputable def p23271 :=
nat_lit
  833754890460581458297166060521994666841833693120204843164879496329690747060171566553414770877044109070592250848765280349011325366899050696944755009614752501005156158802781400722621855406513159435262138412501772178873364390024417483891155559144277960814969979418293656717066528212603401623170709025640494926331781782176770726255270670900274030505792571254693820708403131618781035458973140329103512217608511855624282377694281967670596208028642183953404119405386610357970267131676514190185052810213659839681375996725541872861184000000

noncomputable def p23272 :=
nat_lit
  2666691475535525511711669249005672845542437388726683059602367657543141983428775039591059885532298421164337717982269355183872244746776870733384104603870758135061630488929856994041532643685111233678184005035339184784585102075325576202081688875947948101709228257343291036596541441189985937167311760311245146505353949638396684722317868722673498091910871357638132626752994057864434847577593115537321452917272117073437401902968834219787048130259215182042594331767223441291265867899941355290138744749128818511962890625

noncomputable def p23273 :=
nat_lit
  704488610974616450694361857749470453530293575448676626985671494798673873166003019050006012731478359721103055570290158919512171991664016347593278573416645823560037070177366123947173278397415676289059299088577043997163197359151075224233334499683991556635615942649349281800331183384493634415676182535862645394241419832239444147651263938235517738181961671837083055491850790399365908938520272812210873693188082674480045133523692791058851402310990098387085744565906166106865770178433611177447240454317255852443125038081997938511962890625

noncomputable def p23274 :=
nat_lit
  97549322183888030620768429081073376020494542095063966650290901070573817406040073286749528192614160761259293349305537800834325067927188931542536336124926042617603270579925423884546757082562039653925670194262707344928183633632856845615265200419880521415351487591940357835896783800874597989910972955999937906380818468514682174971866668495332061569177730836799177022883166399397381148699857418505110929460195887108041038190230990217459756339351135522548281970430233411882521254406152160251651178794998201242720991616888399124758528000000

noncomputable def p23275 :=
BSN.sin_dyadic_bound_f 1852460112842789150575 1180591620717411303424 7 6
  590295810358705651712 233646220902400000000 p23270 p23271
  p23272 p23273 p23274

noncomputable def p23276 :=
@BSN.binarySplit_of_base6 (BSN.sinEvenP 1852460112842789150575)
  (BSN.sinEvenQ 1180591620717411303424) 0 6 p23270
  p23271 p23272 (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p23277 :=
p23275 p23272 590294955797461894577 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p23276 (Eq.refl true))

noncomputable def p23278 :=
@BSN.binarySplit_of_base6 (BSN.sinOddP 1852460112842789150575) (BSN.sinOddQ 1180591620717411303424)
  0 6 p23273 p23274 p23272
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p23279 :=
p23269
  (BSN.sin_neg_of_bound 1852460112842789150575 1180591620717411303424 false
    590294955797461894577 590295810358705651712 1 233646220902400000000
    (p23277 (p23278 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p23280 :=
p23224 (p23247 (Eq.refl true))
  (@p23248 590294955797461894577 590295810358705651712
    151882404102765411303424 p23150 590294955797461894577
    590295810358705651712 4316757557 p23149
    (p23279 (Eq.refl true)) (Eq.refl true))

noncomputable def p23281 :=
@p23217 true p23210 p23200 p23218
  p23219 p23210 p23200 p23211
  p20924 (p23280 (Eq.refl true)) (Eq.refl true)

noncomputable def p23282 :=
nat_lit
  19615442258289111024811991662604368427413695392692431103324219145586635090616332873236740649997875880445889163513255917468605

noncomputable def p23283 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p23129
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 4 1) Real.pi))
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p23052 (Enclosure.sfrac false 1 16))))
  p23282

noncomputable def p23284 :=
nat_lit
  165263992197562149737978827008192759957101170741070304821162198818601447809077836456297302609928821211897803006255839576064

noncomputable def p23285 :=
nat_lit
  21448840326903925211259895611219133935864062785483914753389619286341796642697172541052560402713798962124109485107422561035350773802560132872806255648272754036238964939399985043

noncomputable def p23286 :=
nat_lit
  1303703024854071095211805240582002023072939771946199200407129887586804031848535491957374320640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p23287 :=
@p23283 p23284 p23285 p23286
  125554215972038049 73786976294838206464 4316757557 p23149
  p23212 p7287 p23213 p23214

noncomputable def p23288 :=
nat_lit 4172044852863020424070781080170038888064622898535140228520108532488561465

noncomputable def p23289 :=
nat_lit 51363482749996449213570580429262939795112467554788972814059460186613991809288248754528943

noncomputable def p23290 :=
@Enclosure.Real.IsNear.mulLit_ff p23129
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 4 1) Real.pi)
  p23288 p18799 p23289 p23234

noncomputable def p23291 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 3 1)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p23292 :=
@p23291 3 1 0 1 p23232
  p18799 p23233 p23234 p23288
  p18799 p23289

noncomputable def p23293 :=
@p23292 p23234 (Enclosure.Real.IsNear.const false 3 1)
  (p23240 d282
    (p23242 (p23244 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p23294 :=
@p23290 p20538 p2930 1 p20548
  p23282 p23284 p23285 p23286
  p23293 d284 (Eq.refl true)

noncomputable def p23295 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p23052 (Enclosure.sfrac false 1 16)))
  (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
    (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 1852460112842789150575))
    (@Nat.cast Real Real.instNatCast 1180591620717411303424))
  true

noncomputable def p23296 :=
@p23295 1852460112842789150575 1180591620717411303424 645
  1180591620717411303424 false 1004433727776304392 590295810358705651712 1
  233646220902400000000
  (@p23251 p23252 p23253 p23254
    1852460112842789150575 1180591620717411303424 645 1180591620717411303424
    (p23268 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_true_div 1852460112842789150575 1180591620717411303424)

noncomputable def p23297 :=
nat_lit
  8453738438111309954334437447623378076323334759971865448501221745425020368011339758818042222544204723625605108698805969197639227355836370870260279720680612088076923983838285074038780981030069617515758666778592641595654115261341172838453684793315564315501260487128781166508629130994317889877000626612210092303718877716458820865378557464963423825017073206962873422819608501180320147160352367671196993171811517696222754030720067372863411492329984470150687645066608976725365451083724687020740988417632842731604495967812722511962890625

noncomputable def p23298 :=
nat_lit
  33350195618423258331886642420879786673673347724808193726595179853187629882406862662136590835081764362823690033950611213960453014675962027877790200384590100040206246352111256028904874216260526377410485536500070887154934575600976699355646222365771118432598799176731746268682661128504136064926828361025619797053271271287070829050210826836010961220231702850187752828336125264751241418358925613164140488704340474224971295107771278706823848321145687358136164776215464414318810685267060567607402112408546393587255039869021674914447360000

noncomputable def p23299 :=
nat_lit
  182725044546585517534234376569833615353227802995791154401964513190854243503218443433566502605842115107656762985635334635966867551725696781755111098112009636965160723527011709614799152311379128354509025509102790697060579065263355990280364503725426903482633062134145548146274904074279863866421854250626626542143403039129299058938537877991000371291028845333174727780218423993424408938753251195357083698476646119818433595050991762660581561152731536562025124724826575930149146936568502765903817093622916591542306475553946738511962890625

noncomputable def p23300 :=
nat_lit
  10838813575987558957863158786785930668943838010562662961143433452285979711782230365194392021401573417917699261033948644537147229769687659060281815124991782513067030064436158209394084120284671072658407799362523038325353737070317427290585022268875613490594609732437817537321864866763844221101219217333326434042313163168298019441318518721703562396575303426311019669209240711044153460966650824278345658828910654123115670910025665579717750704372348391394253552270025934653613472711794684472405686532777577915857887957432044347195392000000

noncomputable def p23301 :=
BSN.cos_dyadic_bound_f 1852460112842789150575 1180591620717411303424 7 6
  590295810358705651712 233646220902400000000 p23297 p23298
  p23272 p23299 p23300

noncomputable def p23302 :=
@BSN.binarySplit_of_base6 (BSN.cosEvenP 1852460112842789150575)
  (BSN.cosEvenQ 1180591620717411303424) 0 6 p23297
  p23298 p23272 (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p23303 :=
p23301 p23272 1004433727776304392 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p23302 (Eq.refl true))

noncomputable def p23304 :=
@BSN.binarySplit_of_base6 (BSN.cosOddP 1852460112842789150575) (BSN.cosOddQ 1180591620717411303424)
  0 6 p23299 p23300 p23272
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p23305 :=
p23296
  (BSN.cos_neg_of_bound 1852460112842789150575 1180591620717411303424 false
    1004433727776304392 590295810358705651712 1 233646220902400000000
    (p23303 (p23304 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p23306 :=
p23287 p23294
  (@p23078 1004433727776304392 590295810358705651712
    151882404102765411303424 p23150 125554215972038049
    73786976294838206464 4316757557 p23149
    (p23305 (Eq.refl true)) (Eq.refl true))

noncomputable def p23307 :=
@Enclosure.Real.IsNear.recentre' p23130 true p23199 p23200
  p23206 p23207 p23199 p23200
  p23201 p20924
  (@p23216 p23206 p23207 p23281
    (p23306 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p23308 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 3 1) p23131)
    (@iteratedDeriv Real (@DenselyNormedField.toNontriviallyNormedField Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal Real Real.instRCLike))
      (@OfNat.ofNat Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
        (Enclosure.sfrac false 12 1))))

noncomputable def p23309 :=
nat_lit
  17331514942836722645081714752580158856969698572577211026952605996632764561813545002038570969833702937597776815013596423093378852809397693967960249135199703875669510289609613229405254127198510589484626338293978111840471524964900880051422555656995277058572932411711758181022431796479976714179362122017099780031585142592889217822218675587512301505543707842333279771458025408115434012673186342461625476217457804945261

noncomputable def p23310 :=
nat_lit
  688739178255430024722695107842105419343196989817947596869329472656029627649669824775899381489441846931454836761278463511543397091632666440999664395309148693786380138866239635235387195860802204956258682576762261049253827410729622768395702950641518663389407351029577359148583143511308055231889630899105914982239468509850854515689100648212756577436540445641450455040000000000000000000000000000000000000000000000000000000000

noncomputable def p23311 :=
nat_lit 8326022528250288880943169666871989705665875800340163686060806281057325777

noncomputable def p23312 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 3 1) p23131)
  (@iteratedDeriv Real (@DenselyNormedField.toNontriviallyNormedField Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal Real Real.instRCLike))
    (@OfNat.ofNat Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
      (Enclosure.sfrac false 12 1)))
  p23311

noncomputable def p23313 :=
nat_lit 2196698781637121415368897454998772388876676738588332893731668124883618757116420954399447494085621

noncomputable def p23314 :=
nat_lit
  521048483894402211841837989231105122430371301542424739840000000000000000000000000000000000000000000000000000000000

noncomputable def p23315 :=
nat_lit
  58514873171148761048276204109993854504967144360835008008971641259115765190746708906299186262400131187502449734721600751096914990475770358728590210306920105724875914613074953731344348314604797267947977631110119431131098856183629

noncomputable def p23316 :=
nat_lit
  11844773043065711480323635013294239465766037117894719018089691452225120183459296312949206610325977157215024800850914559983608856537741198665193842125253152001987113769690322155382272992184436377145866387891513586051123404341248

noncomputable def p23317 :=
nat_lit
  29999132539989085419625309491894703891179289486879329677176569668412763232580010101121108437415201690597011293031760647770609955329829442326540516931910472216121479891032812981418793098328555479727158663181264425280974709630505157589991343067661445285421751360845586493349211428052959558031384793851

noncomputable def p23318 :=
@p23312 p18799 p23313 p23314
  p23315 p23316 p23317 p22372
  p23202 p23144 p23309 p23310

noncomputable def p23319 :=
nat_lit 2775340842750096293647723222290663235221958600113387895353602093685775259

noncomputable def p23320 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 3 1) p23131
  3 1 0 1 p23319 p18799

noncomputable def p23321 :=
nat_lit 732232927212373805122965818332924129625558912862777631243889374961206252372140318133149164695207

noncomputable def p23322 :=
@Enclosure.Real.IsNear.neg
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
          (Enclosure.sfrac false 12 1)))))

noncomputable def p23323 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
        (Enclosure.sfrac false 12 1))))
  p20538

noncomputable def p23324 :=
@p23323 p20539 1 p20541 590292399501880074047
  590295810358705651712 1753476307 p23149 p23319
  p18799 p23321 p23314

noncomputable def p23325 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
        (Enclosure.sfrac false 12 1))))
  true

noncomputable def p23326 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
      (Enclosure.sfrac false 12 1)))
  (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
    (@Nat.cast Real Real.instNatCast 2783710168905582433017)
    (@Nat.cast Real Real.instNatCast 590295810358705651712))
  false

noncomputable def p23327 :=
@p23326 2783710168905582433017 590295810358705651712 259
  1180591620717411303424 true 1180584799003760148094 1180591620717411303424
  1 233646220902400000000
  (@p23153 p18792 p23154 p23155
    2783710168905582433017 590295810358705651712 259 1180591620717411303424
    (p23164 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div 2783710168905582433017 590295810358705651712)

noncomputable def p23328 :=
BSN.sin_reduce3
  (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
    (@Nat.cast Real Real.instNatCast 2783710168905582433017)
    (@Nat.cast Real Real.instNatCast 590295810358705651712))
  (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
    (@Nat.cast Real Real.instNatCast p23166)
    (@Nat.cast Real Real.instNatCast p23167))
  p2138 p2102 false

noncomputable def p23329 :=
nat_lit 820219021793629471639688335169108012007438536584954663659663977403732374699765971208817441383645184

noncomputable def p23330 :=
nat_lit 12303285326904442074595325027536620180111578048774319954894959661055985620496489568132261620754677760

noncomputable def p23331 :=
BSN.cos_dyadic_bound_f 8219430928249903273651 p2602 2 1
  1180591620717411303424 467748782080000000001 p23170 p23329
  p23170 p23170 p23330

noncomputable def p23332 :=
@BSN.binarySplit_of_base (BSN.cosEvenP 8219430928249903273651) (BSN.cosEvenQ p2602)
  0 1 p23170 p23329 p23170
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p23333 :=
p23331 p23170 1180584799003760148094 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p23332 (Eq.refl true))

noncomputable def p23334 :=
@BSN.binarySplit_of_base (BSN.cosOddP 8219430928249903273651) (BSN.cosOddQ p2602)
  0 1 p23170 p23330 p23170
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p23335 :=
@BSN.cos_arg_round false 1180584799003760148094 1180591620717411303424 p23166
  p23167 8219430928249903273651 p2602 467748782080000000001
  467292441804800000000
  (p23333 (p23334 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p23336 :=
p23328 1180584799003760148094 1180591620717411303424 0
  p2139 467292441804800000000 233646220902400000000 p23169
  d102 p23335 (Eq.refl true) (Eq.refl true)

noncomputable def p23337 :=
p23324 d282
  (@p23325 1180584799003760148094 1180591620717411303424
    61694962834439011303424 p23150 590292399501880074047
    590295810358705651712 1753476307 p23149
    (p23327 (p23336 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p23338 :=
@Neg.neg Real Real.instNeg
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p23126
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p23052 (Enclosure.sfrac false 1 16)))))

noncomputable def p23339 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p23338
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 4 1) Real.pi)
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p23052 (Enclosure.sfrac false 1 16)))))

noncomputable def p23340 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p23339
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) p23131)
    (@iteratedDeriv Real (@DenselyNormedField.toNontriviallyNormedField Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal Real Real.instRCLike))
      (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
        (Enclosure.sfrac false 12 1))))

noncomputable def p23341 :=
@Enclosure.Real.IsNear.of_eq
  (@iteratedDeriv Real (@DenselyNormedField.toNontriviallyNormedField Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal Real Real.instRCLike))
    (@OfNat.ofNat Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
      (Enclosure.sfrac false 12 1)))
  (p23051
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p23340
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p23133
        (Zeta.RiemannSiegel.correction
          (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
            (Enclosure.sfrac false 12 1))))))

noncomputable def p23342 :=
@Enclosure.Real.IsNear.recentre'
  (p23051
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p23340
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p23133
        (Zeta.RiemannSiegel.correction
          (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
            (Enclosure.sfrac false 12 1))))))

noncomputable def p23343 :=
nat_lit
  292231586814585731377512751359817404897910008653636189036833288903414773298812252359444996951771177916939308851942598111807228400192429036931027815047989179351109182032698843994701879561946510526598439234745562058884798851263458811665823710422574034214542258600022295946606789768980437533639618495404812211151

noncomputable def p23344 :=
nat_lit
  218899128460721143644375743152397766398441715391720458388042703519913465786096015624058101972678180538207711591162786358568492248985522723490384033826125374090645017921210758786691024477612933120000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p23345 :=
@p23055
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p23340
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p23133
      (Zeta.RiemannSiegel.correction
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
          (Enclosure.sfrac false 12 1)))))
  347286923913144613691821

noncomputable def p23346 :=
nat_lit
  168491437891808301933043016760551694603199616092657978078295617599771514304622429231777452250025056765439541877816959182356846795560236355917012049265303323544118544230344160227385561186183476664143036449

noncomputable def p23347 :=
nat_lit
  10032913020226237310869197622070557910061530690809581488606035047662224110216294903018315384440590765432325303757053790498770584583633048750167493382743608188543746320969475933440520778435368952314936164352

noncomputable def p23348 :=
nat_lit
  1682939929748294715996352680607968436930638907406309184720181583037693591316998446875558527939294785749568512796708164440144105781779568426530484369688544664850842029616998312028764558404496064253023796752039457227447245148824039053649833450907841764201165347271190121916775315176166357

noncomputable def p23349 :=
nat_lit
  370829547862964653271255153127907301221496679118119436492246031062135030196652546205982812015956750498624682530522855399851457645736410124075486529545776713248989584828661760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p23350 :=
@p23345 1180591620717411303424 22849065 1180591620717411303424
  p23346 p23347 p23348 p23349
  p23315 p23316 p23343 p23344

noncomputable def p23351 :=
nat_lit
  505475155751523699999197569546189310372259611788056021280644287267223741640443650035333007176432687660379657757349974000177094842903766091270719750098925661708626166721402738109401051638776415556961976287

noncomputable def p23352 :=
@Enclosure.Real.IsNear.subLit_tt_p p23340
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p23133
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
        (Enclosure.sfrac false 12 1))))
  p23351 p23347

noncomputable def p23353 :=
nat_lit
  1682928590957255174954642463251735548074876798413525749402876138339048157938459757786956122371782259916318172502347495805900274304097874917362302694886085810159991929334084821759829087526955884135989565618928071912374311214879295100926941237069336551550203018279026093340238329576166357

noncomputable def p23354 :=
nat_lit
  1934189266285832505338602234413956377013862591481275436897427848503280150893071886947099301390285578809063763720718116815923545380290460484465471216936992223656719

noncomputable def p23355 :=
nat_lit
  28793048285076456849987446449190283896766061557132266451844835664715760516297522370041860391064901485759493828054533728788532902755163518009654497157537048672862208

noncomputable def p23356 :=
nat_lit
  4900251769167230643660765552833601664394368813180518962619547183729531593985376472335295505894651949870799979912074346947162364631196019186440774629363809989329023548103083400443366644816485365679434892830562667307123695221754789607

noncomputable def p23357 :=
nat_lit
  160260308320183098883632339843470238058626062956722198044853719759525111591165161011710520672819267614029211993569126451714706322227200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p23358 :=
nat_lit
  4851382106840797368113029556311701665297739717836606385225481574766877459298932184740049571772554416791327280311656438496926588661441920549432239227266578669154244878125471948265704869461551793739141998773943330492147399753973237699279828959547337689611146136612265200784409386978843920161283623808962254701570254615060306538591992531760602068255766283620484898619392

noncomputable def p23359 :=
@p23352 p23353 p23349 p23354
  p23355 p23356 p23357 p23358
  p23346 p23347 p23348 p23349

noncomputable def p23360 :=
@Enclosure.Real.IsNear.subLit_ff_n p23339
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) p23131)
    (@iteratedDeriv Real (@DenselyNormedField.toNontriviallyNormedField Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal Real Real.instRCLike))
      (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
        (Enclosure.sfrac false 12 1))))

noncomputable def p23361 :=
nat_lit
  180668974759065694934922575624177926175668867831525457744681274850012781263607771999224259547424418093222652392144235550889344565575488373601672532469720432428616183

noncomputable def p23362 :=
nat_lit
  14396524142538228424993723224595141948383030778566133225922417832357880258148761185020930195532450742879746914027266864394266451377581759004827248578768524336431104

noncomputable def p23363 :=
nat_lit
  9337960958844873776392383064582818555107545446011843885877770883051473470283856309150503024312547877025255495417095645626358571862957407643251922730630873610582493480586990953212050218020281925370321182920591915229250388247

noncomputable def p23364 :=
nat_lit
  754166156800861641805328658086918767334710884502222108446370445927176995723130169466873038460325965242490409381501771537480970928128000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p23365 :=
nat_lit
  126413374261429168770349209419654665763900347425807521890842800793110256512051432717469551677217285069494318353736653004191555655189048814508462883721361790219216571919711184508513417051654326320468511309791

noncomputable def p23366 :=
nat_lit
  1682923999406959389387836191347032989100643848664883980599426140144471485747478666905430426976538283969761900929368273169833297456006001636004925045353711079066304752870085019125045390152610276637365313525882926470958783022572929473579223314200289846064661307132913315100238329576166357

noncomputable def p23367 :=
nat_lit
  7277085283230082197277212728974791043126831543387041518226219449919846680188075468341508645164857538094671392229563217880216583849556866325208126293633614898126330729215553470884015208069085329877817691126609682135887843981397337129434195163646369403100381239773034778166676751715267984715544952689159484544801725373411840561676105797338198615547810741482956257230848

noncomputable def p23368 :=
@p23360 p23361 p23362 p23363
  p23364 p23365 p23347 p23366
  p23349 p23367 p23351 p23347

noncomputable def p23369 :=
@Enclosure.Real.IsNear.subLit_tt_p p23338
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 4 1) Real.pi)
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p23052 (Enclosure.sfrac false 1 16)))))

noncomputable def p23370 :=
nat_lit
  242821271317862638872595086092077213760473850995138940475928164525181189078778343478818789697338444298330624442277494113645260074049555650567791210023049635657225

noncomputable def p23371 :=
nat_lit
  4119698616472221835613239203957649778432692631722814887851333404905977029733814291532164576133135251100207182443472836845317289724955537206207970504954032681429009723212322153212050218020281925370321182920591915229250388247

noncomputable def p23372 :=
nat_lit 2775352861525097216798314325101803549869287901472932460683749565436539669

noncomputable def p23373 :=
nat_lit 220855883097298041197912187592864814478435487109452369765200775161577472

noncomputable def p23374 :=
nat_lit 1802631726137287104600386260332465767857150387799225187954484866353891444444563837829791149851457

noncomputable def p23375 :=
nat_lit
  260524241947201105920918994615552561215185650771212369920000000000000000000000000000000000000000000000000000000000

noncomputable def p23376 :=
nat_lit
  39901805968696903659153084108310449093331001976123562111868568362736853189174728789314976191616674159749682825598039815695539552365997900238903291919254003083237212470081290885864251379877122621675860060695107317095106427704448307429376

noncomputable def p23377 :=
@p23369 p23370 p23362 p23371
  p23364 p23372 p23373 p23374
  p23375 p23376 p23361 p23362

noncomputable def p23378 :=
@Enclosure.Real.IsNear.neg
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p23126
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p23052 (Enclosure.sfrac false 1 16)))))

noncomputable def p23379 :=
@Enclosure.Real.IsNear.mulLit_ff p23126
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p23052 (Enclosure.sfrac false 1 16))))
  p23228

noncomputable def p23380 :=
@p23379 p23229 p23230 p23231
  125554215972038049 73786976294838206464 4316757557 p23149
  p23370 p23362 p23371 p23364

noncomputable def p23381 :=
p23380 (p23245 (Eq.refl true))
  (@p23078 1004433727776304392 590295810358705651712
    151882404102765411303424 p23150 125554215972038049
    73786976294838206464 4316757557 p23149
    (p23305 (Eq.refl true)) (Eq.refl true))

noncomputable def p23382 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 4 1) Real.pi)
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p23052 (Enclosure.sfrac false 1 16))))
  p20538

noncomputable def p23383 :=
@p23382 p2930 1 p20548 590294955797461894577
  590295810358705651712 4316757557 p23149 p23372
  p23373 p23374 p23375

noncomputable def p23384 :=
p23383 d284
  (@p23248 590294955797461894577 590295810358705651712
    151882404102765411303424 p23150 590294955797461894577
    590295810358705651712 4316757557 p23149
    (p23279 (Eq.refl true)) (Eq.refl true))

noncomputable def p23385 :=
@p23368 p23353 p23349
  (@p23377 p23363 p23364
    (@p23378 false p23370 p23362 p23371
      p23364 (p23381 (Eq.refl true)))
    (p23384 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p23386 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1) p23131)
  (@iteratedDeriv Real (@DenselyNormedField.toNontriviallyNormedField Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal Real Real.instRCLike))
    (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
      (Enclosure.sfrac false 12 1)))
  p23319

noncomputable def p23387 :=
nat_lit
  45548774519588611243811305983524633477275716632901784774814323689396463315224306959252417440339100323177228774293735369973473940871949

noncomputable def p23388 :=
nat_lit
  514053994949066655561336601766946453658303028549927266720615309622604545128439700216874391266247555267763179821015618582539650750089705640338546409571501065429806810873201

noncomputable def p23389 :=
nat_lit
  1423397473844750561543580323617688048708505581145564260879632099228376698995336733337340368457717577524139436149833728000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p23390 :=
@p23386 p23373 p23321 p23375
  p23387 p21008 p23388 p23389
  p23365 p23347 p23366 p23349

noncomputable def p23391 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 2 1) p23131
  2 1 0 1 p23319 p18799

noncomputable def p23392 :=
@Neg.neg Real Real.instNeg
  (p23125
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p23052 (Enclosure.sfrac false 1 16)))))

noncomputable def p23393 :=
@Enclosure.Real.IsNear.of_eq
  (@iteratedDeriv Real (@DenselyNormedField.toNontriviallyNormedField Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal Real Real.instRCLike))
    (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
      (Enclosure.sfrac false 12 1)))
  (p23051
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p23392
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p23131
        (Zeta.RiemannSiegel.correction
          (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
            (Enclosure.sfrac false 12 1))))))

noncomputable def p23394 :=
@p23055
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p23392
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p23131
      (Zeta.RiemannSiegel.correction
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
          (Enclosure.sfrac false 12 1)))))
  347286923913144613691821

noncomputable def p23395 :=
nat_lit 131156030887532693206714039951882257071872356517982836995803187503245766513163406014624023762766768765950790369

noncomputable def p23396 :=
nat_lit
  38478521676166483605741250097796497856523182881313912761668255277583712667477744737709244389536050430475222646784

noncomputable def p23397 :=
nat_lit
  2959858605248205356645459832786732022677771310580564079520940238386499137053310735796561732557973878729225294026798706485052072830925695826607315707

noncomputable def p23398 :=
nat_lit
  2411329114770089897703754972980470941875709402191690041073027440080552737307051245924359543455744000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p23399 :=
@p23394 1180591620717411303424 22849065 1180591620717411303424
  p23395 p23396 p23397 p23398
  p23387 p21008 p23388 p23389

noncomputable def p23400 :=
nat_lit 820912344001935018338436034858651850906320782656850258862619115808821969085633485820071558435

noncomputable def p23401 :=
nat_lit 260740604970814219042361048116400404614587954389239840081425977517360806369707098391474864128

noncomputable def p23402 :=
@Enclosure.Real.IsNear.subLit_ff_p p23392
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p23131
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
        (Enclosure.sfrac false 12 1))))
  p23400 p23401

noncomputable def p23403 :=
nat_lit
  333710914240894655831188071171871673845124915092244835276712754564915002188241529131707156282711027147304709357774021

noncomputable def p23404 :=
nat_lit
  153786368518310572046930214464663627617624198384053874114904603760509625303040000000000000000000000000000000000000000000000000000000000

noncomputable def p23405 :=
nat_lit
  121014123303134159949566183028107992518314058268313574614772898976087770033144752667767358754189667353459590657311

noncomputable def p23406 :=
nat_lit
  2954626107393040749726084196278478534787290099629321739887403780069186856428656773513229859343458905223541913730471395322866378380926833081007315707

noncomputable def p23407 :=
nat_lit
  34197702839186070195241150959959476979475728778715016700057367954102265254390328103726829815964100337086660916309666691795956235642414626972594445757596850066146757938121989473349440133519054438485983232

noncomputable def p23408 :=
@p23402 p23403 p23404 p23405
  p23396 p23406 p23398 p23407
  p23395 p23396 p23397 p23398

noncomputable def p23409 :=
@Enclosure.Real.IsNear.neg
  (p23125
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p23052 (Enclosure.sfrac false 1 16)))))

noncomputable def p23410 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p23411 :=
@p23410
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p23052 (Enclosure.sfrac false 1 16))))
  p23232

noncomputable def p23412 :=
@p23411 p18799 p23233 p23234
  590294955797461894577 590295810358705651712 4316757557 p23149
  p23400 p23401 p23403 p23404

noncomputable def p23413 :=
p23412
  (p23240 d282
    (p23242 (p23244 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (@p23248 590294955797461894577 590295810358705651712
    151882404102765411303424 p23150 590294955797461894577
    590295810358705651712 4316757557 p23149
    (p23279 (Eq.refl true)) (Eq.refl true))

noncomputable def p23414 :=
@Enclosure.Real.IsNear.mulLit_ff p23131
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
      (Enclosure.sfrac false 12 1)))
  p23319 p18799 p23321

noncomputable def p23415 :=
nat_lit 43603337449255704117299373323371372097229

noncomputable def p23416 :=
nat_lit 901981537593660887552385068112751

noncomputable def p23417 :=
nat_lit 4627840190124763103101894661072047675801600000000

noncomputable def p23418 :=
@p23055
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p23052 (Enclosure.sfrac false 1 16))))
  347286923913144613691821

noncomputable def p23419 :=
@p23418 1180591620717411303424 22849065 1180591620717411303424
  125554215972038049 73786976294838206464 4316757557 p23149
  p23415 p5940 p23416 p23417

noncomputable def p23420 :=
p23419 p23180
  (@p23078 1004433727776304392 590295810358705651712
    151882404102765411303424 p23150 125554215972038049
    73786976294838206464 4316757557 p23149
    (p23305 (Eq.refl true)) (Eq.refl true))

noncomputable def p23421 :=
@p23414 p23314 p23415 p5940
  p23416 p23417 p23405 p23396
  p23406 p23398
  (@p23322 true p23319 p18799 p23321
    p23314 (p23337 (Eq.refl true)))
  (@p23053 false p23415 p5940 p23416
    p23417
    (BSN.correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
        (Enclosure.sfrac false 12 1))
      (p23054 (Eq.refl true) (Eq.refl true)
        (p22822 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p23420 (Eq.refl true)))

noncomputable def p23422 :=
p23399 p23180
  (p23408
    (@p23409 true p23400 p23401 p23403
      p23404 (p23413 (Eq.refl true)))
    (p23421 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p23423 :=
p23390
  (@p23391 p23321 p23314 p23319
    p23373 p23321 p23375
    (Enclosure.Real.IsNear.const false 2 1)
    (@p23322 true p23319 p18799 p23321
      p23314 (p23337 (Eq.refl true)))
    (Eq.refl true))
  (@p23393 false p23387 p21008 p23388
    p23389
    (BSN.deriv_correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
        (Enclosure.sfrac false 12 1))
      (p23054 (Eq.refl true) (Eq.refl true)
        (p22822 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p23422 (Eq.refl true)))

noncomputable def p23424 :=
nat_lit
  44358743606192661648345089724081823028420667558942933419923067641837373725788483157588187529288007404465974671281894676811

noncomputable def p23425 :=
nat_lit
  330527984395124299475957654016385519914202341482140609642324397637202895618155672912594605219857642423795606012511679152128

noncomputable def p23426 :=
nat_lit
  305772628665464776611741435557433423072072579430016712862678043354349334077656477130105971250962412358579711166234783806893107965115007161698261778447104213862946386459848711179944107

noncomputable def p23427 :=
@Enclosure.Real.IsNear.mulLit_tf p23133
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
      (Enclosure.sfrac false 12 1)))
  p23424 p23425 p23426

noncomputable def p23428 :=
nat_lit
  34629611597686263466563576702959428737874962692320916260814387639024482095976724005117755392000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p23429 :=
@Enclosure.Real.IsNear.neg
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 4 1)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) Real.pi Real.pi))
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
          (Enclosure.sfrac false 12 1)))))

noncomputable def p23430 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 4 1)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) Real.pi Real.pi))
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
        (Enclosure.sfrac false 12 1))))
  p20550

noncomputable def p23431 :=
@p23430 p20555 p20551 p20557
  2006693138922714179 590295810358705651712 1753476307 p23149
  p23424 p23425 p23426 p23428

noncomputable def p23432 :=
p23431 d286
  (@p23060 4013386277845428358 1180591620717411303424
    61694962834439011303424 p23150 2006693138922714179
    590295810358705651712 1753476307 p23149
    (p23165 (p23178 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p23433 :=
@p23427 p23428 p23415 p5940
  p23416 p23417 p23354 p23355
  p23356 p23357
  (@p23429 false p23424 p23425 p23426
    p23428 (p23432 (Eq.refl true)))
  (@p23053 false p23415 p5940 p23416
    p23417
    (BSN.correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
        (Enclosure.sfrac false 12 1))
      (p23054 (Eq.refl true) (Eq.refl true)
        (p22822 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p23420 (Eq.refl true)))

noncomputable def p23434 :=
p23350 p23180
  (p23359
    (p23385 (p23423 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true))
    (p23433 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p23435 :=
@p23342 false p23315 p23316 p23343
  p23344 p23315 p23316 p23317
  p22372 (p23434 (Eq.refl true)) (Eq.refl true)

noncomputable def p23436 :=
p23318
  (@p23320 p23321 p23314 p23311
    p18799 p23313 p23314
    (Enclosure.Real.IsNear.const false 3 1)
    (@p23322 true p23319 p18799 p23321
      p23314 (p23337 (Eq.refl true)))
    (Eq.refl true))
  (@p23341 false p23315 p23316 p23317
    p22372
    (BSN.iteratedDeriv_two_correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
        (Enclosure.sfrac false 12 1))
      (p23054 (Eq.refl true) (Eq.refl true)
        (p22822 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    p23435)

noncomputable def p23437 :=
@p23308 false p23202 p23144 p23309
  p23310 p23202 p23144 p23203
  p20924 (p23436 (Eq.refl true)) (Eq.refl true)

noncomputable def p23438 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 3 1) p23133)
    (@iteratedDeriv Real (@DenselyNormedField.toNontriviallyNormedField Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal Real Real.instRCLike))
      (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
        (Enclosure.sfrac false 12 1))))

noncomputable def p23439 :=
nat_lit
  7168494211080649555520159591763160339058405651487328828355491861746636305856456762685321644933867691852153591339176879132917390084691154498855114431474882757921433895165491482864877809143178588287719436419631910140100145157587197405579648502091232622162905219283779693506320351329068041010726119791861377693223148136370939077021248772817333421542279842064616047011435771

noncomputable def p23440 :=
nat_lit
  49291701668371503908300367917232651012132300283947473853521450189164507053492656858528983483756622430569014217358405272720459882059389168509572894989419347030315425674923035260993278584452967662723281375461376000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p23441 :=
nat_lit
  133076230818577984945035269172245469085262002676828800259769202925512121177365449472764562587864022213397924013845684030433

noncomputable def p23442 :=
@Enclosure.Real.IsNear.mulLit_tf
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 3 1) p23133)
  (@iteratedDeriv Real (@DenselyNormedField.toNontriviallyNormedField Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal Real Real.instRCLike))
    (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
      (Enclosure.sfrac false 12 1)))
  p23441

noncomputable def p23443 :=
nat_lit
  917317885996394329835224306672300269216217738290050138588034130063048002232969431390317913752887237075739133498704351420679323895345021485094785335341312641588839159379546133539832321

noncomputable def p23444 :=
@p23442 p23425 p23443 p23428
  p23387 p21008 p23388 p23389
  p23193 p23194 p23439 p23440

noncomputable def p23445 :=
@Enclosure.Real.IsNear.mulLit_ft (Enclosure.sfrac false 3 1) p23133
  3 1 0 1 p23424 p23425

noncomputable def p23446 :=
p23444
  (@p23445 p23426 p23428 p23441
    p23425 p23443 p23428
    (Enclosure.Real.IsNear.const false 3 1)
    (@p23429 false p23424 p23425 p23426
      p23428 (p23432 (Eq.refl true)))
    (Eq.refl true))
  (@p23393 false p23387 p21008 p23388
    p23389
    (BSN.deriv_correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
        (Enclosure.sfrac false 12 1))
      (p23054 (Eq.refl true) (Eq.refl true)
        (p22822 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p23422 (Eq.refl true)))

noncomputable def p23447 :=
@p23438 true p23193 p23194 p23439
  p23440 p23193 p23194 p23195
  p22175 (p23446 (Eq.refl true)) (Eq.refl true)

noncomputable def p23448 :=
@p23197 p23189 p22175
  (@p23205 p23192 p20904
    (p23307 (Eq.refl true)) p23437 (Eq.refl true)
    (Eq.refl true))
  p23447 (Eq.refl true) (Eq.refl true)

noncomputable def p23449 :=
@Enclosure.Real.IsNear.recentre' p23134 true p23181 p23144
  p23189 p22175 p23181 p23144
  p23183 p20578 p23448

noncomputable def p23450 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p23135
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
        (Enclosure.sfrac false 12 1))))
  true p23184

noncomputable def p23451 :=
nat_lit
  515230110594918863356141183259665801685909228337512432181433318536361835946210367719186892710961378171719875325071693405605713149814464133436614433589636826002811172788334276354124587376862563238146332672771792317502227156335309587615579431153369332667871261337062539435556712107233926548755519578571725936322504588543507

noncomputable def p23452 :=
nat_lit
  10651124421615482917947356190484469819091701491214368005866441609091654130188779475125884995862728357612151956873933116953454091387190088582131391588516105045065187983360000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p23453 :=
nat_lit
  61350004380558991197168299575573077482789725499650579021937210129664135116205386085684026479858499704111541540545522547930642343478900958909692578848799736972663905935474210531

noncomputable def p23454 :=
nat_lit
  247330401473104534060502521019647190035131349101211839914063056092897225106531867170316401061243044989597671426016139339351365034306751209967546155101893167916606772148699136

noncomputable def p23455 :=
nat_lit
  127687375104712762934385621063071740946254714839465682963697752022321153279077188854633216376387927582234773791501063688977838883876277160967757307041185732219477047430228888553648960629208540300021394727501135746883961466530131641765010624798603107228787765020180223007

noncomputable def p23456 :=
@Enclosure.Real.IsNear.mulLit_tf p23135
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
      (Enclosure.sfrac false 12 1)))
  p23453 p23454 p23455

noncomputable def p23457 :=
nat_lit
  2301532460940129522110988336446895652266573744208441493061433245627371202768341581624978755066912735725373563786321324272097689600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p23458 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 8 1)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) Real.pi Real.pi) Real.pi))
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
        (Enclosure.sfrac false 12 1))))

noncomputable def p23459 :=
@p23458 p20559 p13788 p20560
  p20561 590292399501880074047 590295810358705651712 1753476307
  p23149 p23453 p23454 p23455

noncomputable def p23460 :=
@p23459 p23457 d287
  (@p23325 1180584799003760148094 1180591620717411303424
    61694962834439011303424 p23150 590292399501880074047
    590295810358705651712 1753476307 p23149
    (p23327 (p23336 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p23461 :=
@p23456 p23457 p23415 p5940
  p23416 p23417 p23184 p23185
  p23451 p23452 (p23460 (Eq.refl true))
  (@p23053 false p23415 p5940 p23416
    p23417
    (BSN.correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
        (Enclosure.sfrac false 12 1))
      (p23054 (Eq.refl true) (Eq.refl true)
        (p22822 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p23420 (Eq.refl true)))

noncomputable def p23462 :=
p23188 (p23449 (Eq.refl true))
  (@p23450 p23185 p23451 p23452
    p23184 p23185 p23186 p20578
    (p23461 (Eq.refl true)) (Eq.refl true))
  (Eq.refl true)

noncomputable def p23463 :=
@p23137 false p23138 p23139 p23140
  p23141 p23121 p20904 p23122
  p23123
  (p23147 p23180 (p23462 (Eq.refl true))
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p23464 :=
@p23124 p23118
  (@p23136 false p23121 p20904 p23122
    p23123
    (BSN.iteratedDeriv_three_correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
        (Enclosure.sfrac false 12 1))
      (p23054 (Eq.refl true) (Eq.refl true)
        (p22822 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    p23463)

noncomputable def p23465 :=
@Enclosure.Real.IsNear.recentre' p23115 false p23117 p23118
  p23119 p23118 p23111 p22472
  p23113 p23114
  (p23464 d288 (Eq.refl true))

noncomputable def p23466 :=
@p23112 p23113 p23114 168422943 2147483648
  1 8589934592 p23108 p23109 p23110
  p20890
  (@p23116 p22472 p23113 p23114
    (BSN.correctionLinear_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p22819
        (Enclosure.sfrac false 12 1)))
    (@Enclosure.Real.IsNear.neg p23115 false p23111 p22472
      p23113 p23114 (p23465 (Eq.refl true))))

noncomputable def p23467 :=
@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv p22819) false
  1347383544 17179869184 2 17179869184 168422943 2147483648

noncomputable def p23468 :=
@Enclosure.Real.IsNear.inv_image p22819 219052627181 17179869184 41
  17179869184 673691771 673691773 8589934592
  (p23036 (Eq.refl true)) (Eq.refl true) (Eq.refl true)

noncomputable def p23469 :=
@p23107 p23108 p23109 p23110
  p20890 p23047 p23042 p23048
  p23042
  (p23466
    (@p23467 1 8589934592
      (p23468 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (Eq.refl true))
    (Eq.refl true))

noncomputable def p23470 :=
@p23040 false p23041 p23042 p23043
  p23044 p23019 p22175 p23020
  p22175
  (p23106 (p23469 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p23471 :=
@p23021 p23016
  (@p23023 8589934592
    (@p2563 1 0 1
      (BSN.neg_one_pow_even_mk 12 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1))
    p23039 (Eq.refl true))
  p23470 (Eq.refl true)

noncomputable def p23472 :=
@Enclosure.Real.IsNear.recentre' p22820 false p23015 p23016
  p23017 p23016 p22824 p20588
  p22825 p22175 p23471

noncomputable def p23473 :=
@p22821 p20588 p22814 p22175
  (BSN.hardyZApproximantRS_eq
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
      true 5)
    12
    (p22822 (Eq.refl true) (Eq.refl true)
      (Eq.refl true)))
  (p23014 (p23472 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

theorem d289 : p22813 p22814 p22175 :=
@p22815 p20588 p22814 p22175
  (@Eq.refl Real
    (hardyZApproximantRS
      (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
        true 5)))
  p23473

noncomputable def p23474 :=
Enclosure.Real.IsNear
  (hardyZErrorBoundRS
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
      true 5))
  false 5927655089 549755813888

noncomputable def p23475 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Real.sqrt p22170)
  (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
      true 5)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@OfNat.ofNat Real 2
        (@instOfNatAtLeastTwo Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p23476 :=
@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 25 4) (@Inv.inv Real Real.instInv p23475))
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 1 32)
    (@Inv.inv Real Real.instInv
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p23475
          p23475)
        p23475)))

noncomputable def p23477 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZErrorBoundRS
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
      true 5))
  p23476 false 5927655089

noncomputable def p23478 :=
BSN.hardyZErrorBoundRS_mk
  (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
    true 5)
  102026600 100000
  (Enclosure.sfrac_ofScientific_eq 102026600 5 100000 (Eq.refl true))
  (Eq.refl true)

noncomputable def p23479 :=
@Enclosure.Real.IsNear.addLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 25 4) (@Inv.inv Real Real.instInv p23475))
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 1 32)
    (@Inv.inv Real Real.instInv
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p23475
          p23475)
        p23475)))

noncomputable def p23480 :=
@p23479 740956875 68719476736 25 68719476736 89
  549755813888 1 549755813888 407345355987567509504 5927655089
  549755813888

noncomputable def p23481 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 25 4)
  (@Inv.inv Real Real.instInv p23475) 25 4 0 1
  29638275 17179869184

noncomputable def p23482 :=
@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv p23475) false 29638275
  17179869184 1 17179869184 29638275 17179869184

noncomputable def p23483 :=
nat_lit 85541456749865000545410841

noncomputable def p23484 :=
@Enclosure.Real.IsNear.mulLit_ff (Real.sqrt p22170)
  (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
      true 5)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@OfNat.ofNat Real 2
        (@instOfNatAtLeastTwo Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p23485 :=
@p23484 61327214459 17179869184 7 17179869184
  1394836819256699 8589934592000 510133 8589934592000 p23483
  147573952589676412928000 41048893631980871

noncomputable def p23486 :=
@p23485 147573952589676412928000
  (p22381
    (p22390 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (p22385 (p22387 (Eq.refl true))) (Eq.refl true)

noncomputable def p23487 :=
@Enclosure.Real.IsNear.inv_image p23475 p23483 147573952589676412928000
  41048893631980871 147573952589676412928000 14819137 14819138
  8589934592 p23486 (Eq.refl true) (Eq.refl true)

noncomputable def p23488 :=
@p23480 201 549755813888
  (@p23481 1 17179869184 740956875 68719476736 25
    68719476736 (Enclosure.Real.IsNear.const false 25 4)
    (@p23482 1 17179869184
      (p23487 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (Eq.refl true))
    (Eq.refl true))

noncomputable def p23489 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 1 32)
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p23475
        p23475)
      p23475))
  1

noncomputable def p23490 :=
@p23489 32 0 1 89 17179869184 1
  17179869184 89 549755813888 1 549755813888

noncomputable def p23491 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p23475
        p23475)
      p23475))
  false

noncomputable def p23492 :=
nat_lit 625935993525183059087475726312939872716256645326137528645248886801091285453321

noncomputable def p23493 :=
@Enclosure.Real.IsNear.inv_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p23475
      p23475)
    p23475)
  p23492 p3667

noncomputable def p23494 :=
nat_lit 901106235755583886402965092208145517831883925214719892706827800802807

noncomputable def p23495 :=
nat_lit 7317340822889024462487993957617992870402985480327281

noncomputable def p23496 :=
nat_lit 7022764320184812698853726563557890005963663

noncomputable def p23497 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p23475
    p23475)
  p23475 p23495 p3671 p23496

noncomputable def p23498 :=
@Enclosure.Real.IsNear.mulLit_ff p23475 p23475 p23483
  147573952589676412928000 41048893631980871 147573952589676412928000
  p23483 147573952589676412928000 41048893631980871
  147573952589676412928000 p23495

noncomputable def p23499 :=
@p23497 p3671 p23483 147573952589676412928000
  41048893631980871 147573952589676412928000 p23492 p3667
  p23494 p3667
  (@p23498 p3671 p23496 p3671
    p23486 p23486 (Eq.refl true))
  p23486

noncomputable def p23500 :=
@p23493 p23494 p3667 44 45
  8589934592 (p23499 (Eq.refl true)) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p23501 :=
p23490 (Enclosure.Real.IsNear.const false 1 32)
  (@p23491 89 17179869184 1 17179869184 89
    17179869184 1 17179869184 (p23500 (Eq.refl true))
    (Eq.refl true))

theorem d290 : p23474 201 549755813888 :=
@p23477 549755813888 201 549755813888
  (p23478 (Eq.refl true))
  (p23488 (p23501 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p23502 :=
Enclosure.Real.IsNear
  (hardyZErrorBoundRS
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
      true 5))
  false 5918727087 549755813888

noncomputable def p23503 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Real.sqrt p22819)
  (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
      true 5)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@OfNat.ofNat Real 2
        (@instOfNatAtLeastTwo Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p23504 :=
@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 25 4) (@Inv.inv Real Real.instInv p23503))
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 1 32)
    (@Inv.inv Real Real.instInv
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p23503
          p23503)
        p23503)))

noncomputable def p23505 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZErrorBoundRS
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
      true 5))
  p23504 false 5918727087

noncomputable def p23506 :=
BSN.hardyZErrorBoundRS_mk
  (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
    true 5)
  102149700 100000
  (Enclosure.sfrac_ofScientific_eq 102149700 5 100000 (Eq.refl true))
  (Eq.refl true)

noncomputable def p23507 :=
@Enclosure.Real.IsNear.addLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 25 4) (@Inv.inv Real Real.instInv p23503))
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 1 32)
    (@Inv.inv Real Real.instInv
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p23503
          p23503)
        p23503)))

noncomputable def p23508 :=
@p23507 739840875 68719476736 25 68719476736 87
  549755813888 1 549755813888 406731828361829548032 5918727087
  549755813888

noncomputable def p23509 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 25 4)
  (@Inv.inv Real Real.instInv p23503) 25 4 0 1
  29593635 17179869184

noncomputable def p23510 :=
@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv p23503) false 29593635
  17179869184 1 17179869184 29593635 17179869184

noncomputable def p23511 :=
nat_lit 171340977105781522050531723

noncomputable def p23512 :=
@Enclosure.Real.IsNear.mulLit_ff (Real.sqrt p22819)
  (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
      true 5)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@OfNat.ofNat Real 2
        (@instOfNatAtLeastTwo Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p23513 :=
@p23512 61345704653 17179869184 7 17179869184
  2793039513931191 17179869184000 1021497 17179869184000
  p23511 295147905179352825856000 82215729870594357

noncomputable def p23514 :=
@p23513 295147905179352825856000
  (p23028
    (p23037 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (p23032 (p23034 (Eq.refl true))) (Eq.refl true)

noncomputable def p23515 :=
@Enclosure.Real.IsNear.inv_image p23503 p23511 295147905179352825856000
  82215729870594357 295147905179352825856000 14796817 14796818
  8589934592 p23514 (Eq.refl true) (Eq.refl true)

noncomputable def p23516 :=
@p23508 201 549755813888
  (@p23509 1 17179869184 739840875 68719476736 25
    68719476736 (Enclosure.Real.IsNear.const false 25 4)
    (@p23510 1 17179869184
      (p23515 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (Eq.refl true))
    (Eq.refl true))

noncomputable def p23517 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 1 32)
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p23503
        p23503)
      p23503))
  1

noncomputable def p23518 :=
@p23517 32 0 1 87 17179869184 1
  17179869184 87 549755813888 1 549755813888

noncomputable def p23519 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p23503
        p23503)
      p23503))
  false

noncomputable def p23520 :=
nat_lit 5030182218437667751672577026597719017575976651948014603468715149392620844230067

noncomputable def p23521 :=
@Enclosure.Real.IsNear.inv_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p23503
      p23503)
    p23503)
  p23520 p5990

noncomputable def p23522 :=
nat_lit 7241001708786655899114568785681370031287834898400520445258531015481933

noncomputable def p23523 :=
nat_lit 29357730435563947684560027983953871138998267029348729

noncomputable def p23524 :=
nat_lit 28173846985744677720701792438287148226817671

noncomputable def p23525 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p23503
    p23503)
  p23503 p23523 p5994 p23524

noncomputable def p23526 :=
@Enclosure.Real.IsNear.mulLit_ff p23503 p23503 p23511
  295147905179352825856000 82215729870594357 295147905179352825856000
  p23511 295147905179352825856000 82215729870594357
  295147905179352825856000 p23523

noncomputable def p23527 :=
@p23525 p5994 p23511 295147905179352825856000
  82215729870594357 295147905179352825856000 p23520 p5990
  p23522 p5990
  (@p23526 p5994 p23524 p5994
    p23514 p23514 (Eq.refl true))
  p23514

noncomputable def p23528 :=
@p23521 p23522 p5990 43 44
  8589934592 (p23527 (Eq.refl true)) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p23529 :=
p23518 (Enclosure.Real.IsNear.const false 1 32)
  (@p23519 87 17179869184 1 17179869184 87
    17179869184 1 17179869184 (p23528 (Eq.refl true))
    (Eq.refl true))

theorem d291 : p23502 201 549755813888 :=
@p23505 549755813888 201 549755813888
  (p23506 (Eq.refl true))
  (p23516 (p23529 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p23530 :=
@LE.le Real Real.instLE
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@OfNat.ofNat Real 32
      (@instOfNatAtLeastTwo Real 32 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 31 (instOfNatNat 31))
          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 30 (instOfNatNat 30))))))
    Real.pi)
  (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE d64))

noncomputable def p23531 :=
@OfNat.ofNat Real 510133
  (@instOfNatAtLeastTwo Real 510133
    (@AddMonoidWithOne.toNatCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real
            (@DivisionSemiring.toSemiring Real
              (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField)))))))
    (Mathlib.Meta.NormNum.instAtLeastTwo 510131))

noncomputable def p23532 :=
@LE.le Real Real.instLE
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@OfNat.ofNat Real 32
      (@instOfNatAtLeastTwo Real 32 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 31 (instOfNatNat 31))
          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 30 (instOfNatNat 30))))))
    Real.pi)
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField))))))
    p23531 p4068)

noncomputable def p23533 :=
@congrArg Real Prop (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE d64))
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField))))))
    p23531 p4068)

noncomputable def p23534 :=
p23533
  (@LE.le Real Real.instLE
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@OfNat.ofNat Real 32
        (@instOfNatAtLeastTwo Real 32 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 31 (instOfNatNat 31))
            (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 30 (instOfNatNat 30))))))
      Real.pi))

noncomputable def p23535 :=
@Mathlib.Meta.NormNum.IsNNRat.to_eq Real
  (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField)) 510133 500
  (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE d64)) p23531
  p4068
  (@Mathlib.Meta.NormNum.isNNRat_ofScientific_of_true Real
    (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField)) 102026600
    5 510133 500
    (p383
      (p384 p4
        (@p385 510133 500
          (p389 (@Eq.refl Nat (Nat.mul 102026600 1))
            (@Eq.refl Nat 100000))))))
  (@Eq.refl Real p23531)

noncomputable def p23536 :=
@congrArg Real Prop
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField))))))
    p23531 p4068)

noncomputable def p23537 :=
@p23536
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField))))))
    p23531 p4068)

noncomputable def p23538 :=
p23537
  (@LE.le Real Real.instLE
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@OfNat.ofNat Real 32
        (@instOfNatAtLeastTwo Real 32 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 31 (instOfNatNat 31))
            (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 30 (instOfNatNat 30))))))
      Real.pi))

noncomputable def p23539 :=
@Mathlib.Meta.NormNum.IsNNRat.to_eq Real
  (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField)) 510133 500
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField))))))
    p23531 p4068)

noncomputable def p23540 :=
@Mathlib.Meta.NormNum.isNNRat_mul Real
  (@DivisionSemiring.toSemiring Real
    (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField)))
  (@HMul.hMul Real Real Real
    (@instHMul Real (@Distrib.toMul Real (@instDistribOfSemiring Real Real.semiring))))
  p23531
  (@Inv.inv Real
    (@InvOneClass.toInv Real
      (@DivInvOneMonoid.toInvOneClass Real
        (@DivisionMonoid.toDivInvOneMonoid Real
          (@GroupWithZero.toDivisionMonoid Real
            (@DivisionSemiring.toGroupWithZero Real
              (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField)))))))
    p4068)

noncomputable def p23541 :=
@p23540 510133 1 510133 1 500 500
  1
  (@Eq.refl (Real → Real → Real)
    (@HMul.hMul Real Real Real
      (@instHMul Real (@Distrib.toMul Real (@instDistribOfSemiring Real Real.semiring)))))
  (@Mathlib.Meta.NormNum.IsNat.to_isNNRat Real
    (@DivisionSemiring.toSemiring Real
      (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField)))
    p23531 510133
    (@Mathlib.Meta.NormNum.isNat_ofNat Real
      (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing))
      p23531 510133
      (@Eq.refl Real
        (@OfNat.ofNat Real 510133
          (@instOfNatAtLeastTwo Real 510133
            (@AddMonoidWithOne.toNatCast Real
              (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 510131))))))

noncomputable def p23542 :=
@p23539 p23531 p4068
  (@Mathlib.Meta.NormNum.isNNRat_div Real
    (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField)) p23531
    p4068 510133 500
    (p23541 p4091 (@Eq.refl Nat (Nat.mul 510133 1))
      (@Eq.refl Nat 500)))
  (@Eq.refl Real p23531)

noncomputable def p23543 :=
@le_of_not_gt Real Real.linearOrder
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@OfNat.ofNat Real 32
      (@instOfNatAtLeastTwo Real 32 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 31 (instOfNatNat 31))
          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 30 (instOfNatNat 30))))))
    Real.pi)
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField))))))
    p23531 p4068)

noncomputable def p23544 :=
@LT.lt Real
  (@Preorder.toLT Real (@PartialOrder.toPreorder Real (@LinearOrder.toPartialOrder Real Real.linearOrder)))
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField))))))
    p23531 p4068)

noncomputable def p23545 :=
@HMul.hMul Real Real Real
  (@instHMul Real (@Distrib.toMul Real (@instDistribOfSemiring Real Real.semiring)))
  (@OfNat.ofNat Real 459733
    (@instOfNatAtLeastTwo Real 459733
      (@AddMonoidWithOne.toNatCast Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne Real
          (@NonAssocSemiring.toAddCommMonoidWithOne Real (@Semiring.toNonAssocSemiring Real Real.semiring))))
      (@Nat.instAtLeastTwoHAddOfNat
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) 459731
          (@OfNat.ofNat Nat 1 (instOfNatNat 1)))
        (@instNeZeroNatHAdd_1 459731 (@OfNat.ofNat Nat 1 (instOfNatNat 1))
          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 0 (instOfNatNat 0)))))))

noncomputable def p23546 :=
@HMul.hMul Real Real Real
  (@instHMul Real
    (@Distrib.toMul Real
      (@instDistribOfSemiring Real
        (@DivisionSemiring.toSemiring Real
          (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField))))))
  (@OfNat.ofNat Real 1
    (@One.toOfNat1 Real
      (@AddMonoidWithOne.toOne Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))))
  p23531

noncomputable def p23547 :=
@HSub.hSub Real Real Real
  (@instHSub Real
    (@SubNegMonoid.toSub Real
      (@AddGroup.toSubNegMonoid Real
        (@AddGroupWithOne.toAddGroup Real
          (@Ring.toAddGroupWithOne Real
            (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField)))))))
  p23546
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real
          (@DivisionSemiring.toSemiring Real
            (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField))))))
    p3705 (p8250 Real.pi))

noncomputable def p23548 :=
@HAdd.hAdd Real Real Real
  (@instHAdd Real (@AddSemigroup.toAdd Real (@AddMonoid.toAddSemigroup Real Real.instAddMonoid)))
  (p23545
    (@Neg.neg Real
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
                (@Semiring.toNonAssocSemiring Real Real.semiring))))))))
  p23547

noncomputable def p23549 :=
@Eq.mp
  (@LT.lt Real (@Preorder.toLT Real (@PartialOrder.toPreorder Real Real.partialOrder))
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real (@AddSemigroup.toAdd Real (@AddMonoid.toAddSemigroup Real Real.instAddMonoid)))
      p23548 (p8253 p3713))
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real (@MulZeroClass.toZero Real (@instMulZeroClassOfSemiring Real Real.semiring)))))
  (@LT.lt Real (@Preorder.toLT Real (@PartialOrder.toPreorder Real Real.partialOrder))
    (@OfNat.ofNat Real 0 (@Zero.toOfNat0 Real Real.instZero))
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real (@MulZeroClass.toZero Real (@instMulZeroClassOfSemiring Real Real.semiring)))))

noncomputable def p23550 :=
@Mathlib.Tactic.Ring.Common.add_congr Real Real.instCommSemiring p23548
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Nat.rawCast Real
      (@Mathlib.Meta.NormNum.instAddMonoidWithOne Real
        (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing)))
      50400)
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      p8255
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))))
  (p8253 p3713)

noncomputable def p23551 :=
@p23550
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 50400))
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      p8257
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))))
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))

noncomputable def p23552 :=
@Mathlib.Tactic.Ring.Common.add_congr Real Real.instCommSemiring
  (p23545
    (@Neg.neg Real
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
                (@Semiring.toNonAssocSemiring Real Real.semiring))))))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 459733))
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))

noncomputable def p23553 :=
@p23552 p23547
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      510133)
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      p8255
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Nat.rawCast Real
      (@Mathlib.Meta.NormNum.instAddMonoidWithOne Real
        (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing)))
      50400)
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      p8255
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))))

noncomputable def p23554 :=
@Mathlib.Tactic.Ring.Common.mul_congr Real Real.instCommSemiring
  (@OfNat.ofNat Real 459733
    (@instOfNatAtLeastTwo Real 459733
      (@AddMonoidWithOne.toNatCast Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne Real
          (@NonAssocSemiring.toAddCommMonoidWithOne Real (@Semiring.toNonAssocSemiring Real Real.semiring))))
      (@Nat.instAtLeastTwoHAddOfNat
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) 459731
          (@OfNat.ofNat Nat 1 (instOfNatNat 1)))
        (@instNeZeroNatHAdd_1 459731 (@OfNat.ofNat Nat 1 (instOfNatNat 1))
          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 0 (instOfNatNat 0)))))))

noncomputable def p23555 :=
@p23554
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      459733)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (@Neg.neg Real
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

noncomputable def p23556 :=
@Mathlib.Tactic.Ring.cast_pos Real Real.instCommSemiring
  (@OfNat.ofNat Real 459733
    (@instOfNatAtLeastTwo Real 459733
      (@AddMonoidWithOne.toNatCast Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne Real
          (@NonAssocSemiring.toAddCommMonoidWithOne Real (@Semiring.toNonAssocSemiring Real Real.semiring))))
      (@Nat.instAtLeastTwoHAddOfNat
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) 459731
          (@OfNat.ofNat Nat 1 (instOfNatNat 1)))
        (@instNeZeroNatHAdd_1 459731 (@OfNat.ofNat Nat 1 (instOfNatNat 1))
          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 0 (instOfNatNat 0)))))))

noncomputable def p23557 :=
@Mathlib.Meta.NormNum.isNat_ofNat Real
  (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing))
  (@OfNat.ofNat Real 459733
    (@instOfNatAtLeastTwo Real 459733
      (@AddMonoidWithOne.toNatCast Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne Real
          (@NonAssocSemiring.toAddCommMonoidWithOne Real (@Semiring.toNonAssocSemiring Real Real.semiring))))
      (@Nat.instAtLeastTwoHAddOfNat
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) 459731
          (@OfNat.ofNat Nat 1 (instOfNatNat 1)))
        (@instNeZeroNatHAdd_1 459731 (@OfNat.ofNat Nat 1 (instOfNatNat 1))
          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 0 (instOfNatNat 0)))))))

noncomputable def p23558 :=
@p23555
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 1))
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 459733))
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (@p23556 459733
    (@p23557 459733
      (@Eq.refl Real
        (@OfNat.ofNat Real 459733
          (@instOfNatAtLeastTwo Real 459733
            (@AddMonoidWithOne.toNatCast Real
              (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 459731))))))

noncomputable def p23559 :=
@Mathlib.Tactic.Ring.Common.add_mul Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    459733)
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 1))
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 459733))
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))

noncomputable def p23560 :=
@Mathlib.Tactic.Ring.Common.mul_add Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    459733)
  (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (Int.negOfNat 1))
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (Int.negOfNat 459733))

noncomputable def p23561 :=
@Mathlib.Meta.NormNum.IsInt.to_raw_eq Real
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      459733)
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 1)))
  (Int.negOfNat 459733)

noncomputable def p23562 :=
@Mathlib.Meta.NormNum.isInt_mul Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real
          (@Ring.toSemiring Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing)))))))
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    459733)
  (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (Int.negOfNat 1))

noncomputable def p23563 :=
@p23562 (Int.ofNat 459733) (Int.negOfNat 1) (Int.negOfNat 459733)
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
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      459733)
    459733
    (@Mathlib.Meta.NormNum.IsNat.of_raw Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      459733))

noncomputable def p23564 :=
@p23560
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 459733))
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (@p23561 (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (p23563
      (@Mathlib.Meta.NormNum.IsInt.of_raw Real
        (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing)) (Int.negOfNat 1))
      (@Eq.refl Int (Int.negOfNat 459733))))
  (@Mathlib.Tactic.Ring.Common.mul_zero Real Real.instCommSemiring
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      459733))

noncomputable def p23565 :=
@p23559
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 459733))
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (p23564
    (@Mathlib.Tactic.Ring.Common.add_pf_add_zero Real Real.instCommSemiring
      (@HAdd.hAdd Real Real Real
        (@instHAdd Real
          (@Distrib.toAdd Real
            (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
        (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
          (Int.negOfNat 459733))
        (@OfNat.ofNat Real 0
          (@Zero.toOfNat0 Real
            (@MulZeroClass.toZero Real
              (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))))

noncomputable def p23566 :=
p23565
  (@Mathlib.Tactic.Ring.Common.zero_mul Real Real.instCommSemiring
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
        (Int.negOfNat 1))
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))))
  (@Mathlib.Tactic.Ring.Common.add_pf_add_zero Real Real.instCommSemiring
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
        (Int.negOfNat 459733))
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))))

noncomputable def p23567 :=
p23553
  (p23558
    (p3726 p3727
      (p3728
        (@Mathlib.Meta.NormNum.IsInt.to_raw_eq Real p3729 (Int.negOfNat 1)
          (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
          (p3733 (@Eq.refl Int (Int.negOfNat 1))))
        (@Mathlib.Tactic.Ring.Common.neg_zero Real Real.commRing)))
    p23566)

noncomputable def p23568 :=
@Mathlib.Tactic.Ring.Common.sub_congr Real Real.commRing p23546
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      510133)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real
          (@DivisionSemiring.toSemiring Real
            (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField))))))
    p3705 (p8250 Real.pi))

noncomputable def p23569 :=
@p3744 p23531
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      510133)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      510133)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))

noncomputable def p23570 :=
p23569
  (p3746
    (p3747
      (@Nat.cast_one Real
        (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing)))))
  (@Mathlib.Tactic.Ring.cast_pos Real Real.instCommSemiring p23531 510133
    (@Mathlib.Meta.NormNum.isNat_ofNat Real
      (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing))
      p23531 510133
      (@Eq.refl Real
        (@OfNat.ofNat Real 510133
          (@instOfNatAtLeastTwo Real 510133
            (@AddMonoidWithOne.toNatCast Real
              (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 510131))))))

noncomputable def p23571 :=
@Mathlib.Tactic.Ring.Common.add_mul Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    1)
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      510133)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      510133)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))

noncomputable def p23572 :=
@Mathlib.Tactic.Ring.Common.mul_add Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    1)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    510133)
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    510133)

noncomputable def p23573 :=
@Mathlib.Meta.NormNum.IsNat.to_raw_eq Real
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      1)
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      510133))
  510133

noncomputable def p23574 :=
@Mathlib.Meta.NormNum.isNat_mul Real (@CommSemiring.toSemiring Real Real.instCommSemiring)
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    1)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    510133)
  1 510133

noncomputable def p23575 :=
@p23574 510133
  (@Eq.refl (Real → Real → Real)
    (@HMul.hMul Real Real Real
      (@instHMul Real
        (@Distrib.toMul Real
          (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (@Mathlib.Meta.NormNum.IsNat.of_raw Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    1)
  (@Mathlib.Meta.NormNum.IsNat.of_raw Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    510133)
  (@Eq.refl Nat 510133)

noncomputable def p23576 :=
@p23572
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      510133)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (@p23573
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    p23575)

noncomputable def p23577 :=
p23576
  (@Mathlib.Tactic.Ring.Common.mul_zero Real Real.instCommSemiring
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      1))
  (@Mathlib.Tactic.Ring.Common.add_pf_add_zero Real Real.instCommSemiring
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      (@Nat.rawCast Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne Real
          (@NonAssocSemiring.toAddCommMonoidWithOne Real
            (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
        510133)
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))))

noncomputable def p23578 :=
@p23571
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      510133)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  p23577

noncomputable def p23579 :=
p23578
  (@Mathlib.Tactic.Ring.Common.zero_mul Real Real.instCommSemiring
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      (@Nat.rawCast Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne Real
          (@NonAssocSemiring.toAddCommMonoidWithOne Real
            (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
        510133)
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))))

noncomputable def p23580 :=
p23579
  (@Mathlib.Tactic.Ring.Common.add_pf_add_zero Real Real.instCommSemiring
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      (@Nat.rawCast Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne Real
          (@NonAssocSemiring.toAddCommMonoidWithOne Real
            (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
        510133)
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))))

noncomputable def p23581 :=
@p23568
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    p8257
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      510133)
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      p8255
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))))
  (p23570 p23580)

noncomputable def p23582 :=
@Mathlib.Tactic.Ring.Common.sub_pf Real Real.commRing
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      510133)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    p8257
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))

noncomputable def p23583 :=
@p23582
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    p8255
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      510133)
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      p8255
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))))
  p8321

noncomputable def p23584 :=
@Mathlib.Tactic.Ring.Common.add_pf_add_lt Real Real.instCommSemiring
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    p8255
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    p8255
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    510133)

noncomputable def p23585 :=
p23583
  (p23584
    (@Mathlib.Tactic.Ring.Common.add_pf_zero_add Real Real.instCommSemiring
      (@HAdd.hAdd Real Real Real
        (@instHAdd Real
          (@Distrib.toAdd Real
            (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
        p8255
        (@OfNat.ofNat Real 0
          (@Zero.toOfNat0 Real
            (@MulZeroClass.toZero Real
              (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))))

noncomputable def p23586 :=
@Mathlib.Tactic.Ring.Common.add_pf_add_overlap Real Real.instCommSemiring
  (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (Int.negOfNat 459733))
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    510133)
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    p8255
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (@Nat.rawCast Real
    (@Mathlib.Meta.NormNum.instAddMonoidWithOne Real
      (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing)))
    50400)
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    p8255
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))

noncomputable def p23587 :=
@Mathlib.Meta.NormNum.IsNat.to_raw_eq Real
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 459733))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      510133))
  50400
  (@Mathlib.Meta.NormNum.instAddMonoidWithOne Real
    (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing)))

noncomputable def p23588 :=
@Mathlib.Meta.NormNum.isInt_add Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (Int.negOfNat 459733))
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    510133)
  (Int.negOfNat 459733) (Int.ofNat 510133)

noncomputable def p23589 :=
@p23588 (Int.ofNat 50400)
  (@Eq.refl (Real → Real → Real)
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))
  (@Mathlib.Meta.NormNum.IsInt.of_raw Real
    (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing)) (Int.negOfNat 459733))
  (@Mathlib.Meta.NormNum.IsNat.to_isInt Real
    (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      510133)
    510133
    (@Mathlib.Meta.NormNum.IsNat.of_raw Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      510133))

noncomputable def p23590 :=
@Mathlib.Meta.NormNum.IsInt.to_isNat Real
  (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 459733))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
      510133))
  50400 (p23589 (@Eq.refl Int (Int.ofNat 50400)))

noncomputable def p23591 :=
p23567
  (p23581
    (p8291 (p8297 p8306) p8315)
    p23585)
  (p23586 (p23587 p23590)
    (@Mathlib.Tactic.Ring.Common.add_pf_zero_add Real Real.instCommSemiring
      (@HAdd.hAdd Real Real Real
        (@instHAdd Real
          (@Distrib.toAdd Real
            (@instDistribOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))
        p8255
        (@OfNat.ofNat Real 0
          (@Zero.toOfNat0 Real
            (@MulZeroClass.toZero Real
              (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring))))))))

noncomputable def p23592 :=
@Mathlib.Tactic.Ring.of_eq Real
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real (@AddSemigroup.toAdd Real (@AddMonoid.toAddSemigroup Real Real.instAddMonoid)))
    p23548 (p8253 p3713))
  (@OfNat.ofNat Real 0 (@Zero.toOfNat0 Real Real.instZero))
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
  (p23551 p23591
    (p8336
      (p3840 (p3842 p3852) p3860)
      p8354)
    (@p8355
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))
      p8358
      (p8363
        (@Mathlib.Tactic.Ring.Common.add_pf_zero_add Real Real.instCommSemiring
          (@OfNat.ofNat Real 0
            (@Zero.toOfNat0 Real
              (@MulZeroClass.toZero Real
                (@instMulZeroClassOfSemiring Real (@CommSemiring.toSemiring Real Real.instCommSemiring)))))))))

noncomputable def p23593 :=
@congrArg Real Prop
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real (@AddSemigroup.toAdd Real (@AddMonoid.toAddSemigroup Real Real.instAddMonoid)))
    p23548 (p8253 p3713))
  (@OfNat.ofNat Real 0 (@Zero.toOfNat0 Real Real.instZero))
  (fun (_a : Real) =>
    @LT.lt Real (@Preorder.toLT Real (@PartialOrder.toPreorder Real Real.partialOrder)) _a
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real (@MulZeroClass.toZero Real (@instMulZeroClassOfSemiring Real Real.semiring)))))
  (p23592
    (@Mathlib.Tactic.Ring.cast_zero Real Real.instCommSemiring
      (@OfNat.ofNat Real 0 (@Zero.toOfNat0 Real Real.instZero))
      (@Mathlib.Meta.NormNum.isNat_ofNat Real
        (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing))
        (@OfNat.ofNat Real 0 (@Zero.toOfNat0 Real Real.instZero)) 0
        (@Nat.cast_zero Real
          (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing))))))

noncomputable def p23594 :=
@HAdd.hAdd Real Real Real
  (@instHAdd Real (@Distrib.toAdd Real (@instDistribOfSemiring Real Real.semiring)))
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real (@instDistribOfSemiring Real (@Ring.toSemiring Real Real.instRing))))
    (@OfNat.ofNat Real 459733
      (@instOfNatAtLeastTwo Real 459733 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 459732 (instOfNatNat 459732))
          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 459731 (instOfNatNat 459731))))))
    (@Neg.neg Real
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
                (@Semiring.toNonAssocSemiring Real Real.semiring))))))))
  p23547

noncomputable def p23595 :=
@Mathlib.Tactic.Linarith.add_neg Real Real.semiring Real.partialOrder Real.instIsStrictOrderedRing
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real (@instDistribOfSemiring Real (@Ring.toSemiring Real Real.instRing))))
    (@OfNat.ofNat Real 459733
      (@instOfNatAtLeastTwo Real 459733 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 459732 (instOfNatNat 459732))
          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 459731 (instOfNatNat 459731))))))
    (@Neg.neg Real
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
                (@Semiring.toNonAssocSemiring Real Real.semiring))))))))
  p23547

noncomputable def p23596 :=
@Mathlib.Tactic.Linarith.mul_neg Real Real.instRing Real.partialOrder Real.instIsStrictOrderedRing
  (@Neg.neg Real
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
  (@OfNat.ofNat Real 459733
    (@instOfNatAtLeastTwo Real 459733 Real.instNatCast
      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 459732 (instOfNatNat 459732))
        (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 459731 (instOfNatNat 459731))))))
  (@neg_neg_of_pos Real Real.instAddCommGroup Real.partialOrder Real.instIsOrderedAddMonoid
    (@OfNat.ofNat Real 1
      (@One.toOfNat1 Real
        (@AddMonoidWithOne.toOne Real
          (@AddCommMonoidWithOne.toAddMonoidWithOne Real
            (@NonAssocSemiring.toAddCommMonoidWithOne Real
              (@Semiring.toNonAssocSemiring Real Real.semiring))))))
    (@Mathlib.Tactic.Linarith.zero_lt_one Real Real.semiring Real.partialOrder Real.instIsStrictOrderedRing))

noncomputable def p23597 :=
@Mathlib.Meta.NormNum.isNat_lt_true Real Real.semiring Real.partialOrder Real.instIsOrderedRing
  (@FloorSemiring.instCharZero Real (@Ring.toSemiring Real Real.instRing) Real.partialOrder
    (@FloorRing.toFloorSemiring Real Real.instRing Real.linearOrder Real.instFloorRing))
  (@OfNat.ofNat Real 0 (@Zero.toOfNat0 Real Real.instZero))
  (@OfNat.ofNat Real 459733
    (@instOfNatAtLeastTwo Real 459733 Real.instNatCast
      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 459732 (instOfNatNat 459732))
        (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 459731 (instOfNatNat 459731))))))
  0 459733
  (@Mathlib.Meta.NormNum.isNat_ofNat Real
    (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing))
    (@OfNat.ofNat Real 0 (@Zero.toOfNat0 Real Real.instZero)) 0
    (@Nat.cast_zero Real
      (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing))))

noncomputable def p23598 :=
p23597
  (@Mathlib.Meta.NormNum.isNat_ofNat Real
    (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing))
    (@OfNat.ofNat Real 459733
      (@instOfNatAtLeastTwo Real 459733 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 459732 (instOfNatNat 459732))
          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 459731 (instOfNatNat 459731))))))
    459733
    (@Eq.refl Real
      (@OfNat.ofNat Real 459733
        (@instOfNatAtLeastTwo Real 459733
          (@AddMonoidWithOne.toNatCast Real
            (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing)))
          (Mathlib.Meta.NormNum.instAtLeastTwo 459731)))))

noncomputable def p23599 :=
@HSub.hSub Real Real Real
  (@instHSub Real
    (@SubNegMonoid.toSub Real
      (@AddGroup.toSubNegMonoid Real
        (@AddGroupWithOne.toAddGroup Real (@Ring.toAddGroupWithOne Real Real.instRing)))))
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField))))))
    p23531 p4068)

noncomputable def p23600 :=
p8371
  (p23599
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@OfNat.ofNat Real 32
        (@instOfNatAtLeastTwo Real 32 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 31 (instOfNatNat 31))
            (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 30 (instOfNatNat 30))))))
      Real.pi))

noncomputable def p23601 :=
@Mathlib.Tactic.CancelDenoms.derive_trans Real Real.instMul
  (p23599
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@OfNat.ofNat Real 32
        (@instOfNatAtLeastTwo Real 32 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 31 (instOfNatNat 31))
            (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 30 (instOfNatNat 30))))))
      Real.pi))

noncomputable def p23602 :=
@p23601
  (p23599
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@OfNat.ofNat Real 32
        (@instOfNatAtLeastTwo Real 32 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 31 (instOfNatNat 31))
            (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 30 (instOfNatNat 30))))))
      Real.pi))

noncomputable def p23603 :=
@p23602
  (@OfNat.ofNat Real 500
    (@instOfNatAtLeastTwo Real 500
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 498)))

noncomputable def p23604 :=
@congrArg Real (Real → Real)
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField))))))
    p23531 p4068)

noncomputable def p23605 :=
@p23604
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField))))))
    p23531 p4068)

noncomputable def p23606 :=
@congrFun' Real Real p23599 p23599
  (p23605
    (@HSub.hSub Real Real Real
      (@instHSub Real
        (@SubNegMonoid.toSub Real
          (@AddGroup.toSubNegMonoid Real
            (@AddGroupWithOne.toAddGroup Real (@Ring.toAddGroupWithOne Real Real.instRing))))))
    (p23542 (@Eq.refl Real p4068)))
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@OfNat.ofNat Real 32
      (@instOfNatAtLeastTwo Real 32 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 31 (instOfNatNat 31))
          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 30 (instOfNatNat 30))))))
    Real.pi)

noncomputable def p23607 :=
@p8380
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField))))))
    p23531 p4068)

noncomputable def p23608 :=
@p23607
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@OfNat.ofNat Real 32
      (@instOfNatAtLeastTwo Real 32 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 31 (instOfNatNat 31))
          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 30 (instOfNatNat 30))))))
    Real.pi)
  p23546

noncomputable def p23609 :=
@p23608
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real
          (@DivisionSemiring.toSemiring Real
            (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField))))))
    p3705 (p8250 Real.pi))

noncomputable def p23610 :=
@HMul.hMul Real Real Real
  (@instHMul Real
    (@inferInstance (Mul Real)
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real
          (@DivisionSemiring.toSemiring Real
            (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField)))))))
  (@OfNat.ofNat Real 1
    (@One.toOfNat1 Real
      (@AddMonoidWithOne.toOne Real
        (@inferInstance (AddMonoidWithOne Real)
          (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))))))
  p23531

noncomputable def p23611 :=
@p8385 p23531 p4068 p23546
  (@rfl Real p23610)
  (p8388 p8397
    (p3747
      (@Nat.cast_one Real
        (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing)))))
  (@p8399 500 p8401
    (@p8295 500
      (@Eq.refl Real
        (@OfNat.ofNat Real 500
          (@instOfNatAtLeastTwo Real 500
            (@AddMonoidWithOne.toNatCast Real
              (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 498))))))

noncomputable def p23612 :=
@Eq.mp
  (@LT.lt Real (@Preorder.toLT Real (@PartialOrder.toPreorder Real Real.partialOrder))
    p23600
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@Ring.toSemiring Real Real.instRing))))))
  (@LT.lt Real (@Preorder.toLT Real (@PartialOrder.toPreorder Real Real.partialOrder))
    p23547
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@Ring.toSemiring Real Real.instRing))))))
  (@congrArg Real Prop p23600 p23547
    (fun (_a : Real) =>
      @LT.lt Real (@Preorder.toLT Real (@PartialOrder.toPreorder Real Real.partialOrder)) _a
        (@OfNat.ofNat Real 0
          (@Zero.toOfNat0 Real
            (@MulZeroClass.toZero Real
              (@instMulZeroClassOfSemiring Real (@Ring.toSemiring Real Real.instRing))))))
    (@p23603 p23547 p23606
      (p23609 p23611 p8407)))

noncomputable def p23613 :=
@Mathlib.Tactic.Linarith.mul_neg Real Real.instRing Real.partialOrder Real.instIsStrictOrderedRing
  (p23599
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@OfNat.ofNat Real 32
        (@instOfNatAtLeastTwo Real 32 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 31 (instOfNatNat 31))
            (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 30 (instOfNatNat 30))))))
      Real.pi))

noncomputable def p23614 :=
@Mathlib.Tactic.Linarith.sub_neg_of_lt Real Real.instRing Real.partialOrder Real.instIsOrderedRing
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField))))))
    p23531 p4068)

noncomputable def p23615 :=
fun
    (a :
      p23544
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (@OfNat.ofNat Real 32
            (@instOfNatAtLeastTwo Real 32 Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 31 (instOfNatNat 31))
                (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 30 (instOfNatNat 30))))))
          Real.pi)) =>
  @Mathlib.Tactic.Linarith.lt_irrefl Real Real.instPreorder
    (@OfNat.ofNat Real 0 (@Zero.toOfNat0 Real Real.instZero))
    (p23549 p23593
      (@Mathlib.Tactic.Linarith.add_neg Real Real.semiring Real.partialOrder Real.instIsStrictOrderedRing
        p23594
        (@HMul.hMul Real Real Real
          (@instHMul Real
            (@Distrib.toMul Real (@instDistribOfSemiring Real (@Ring.toSemiring Real Real.instRing))))
          (@OfNat.ofNat Real 800
            (@instOfNatAtLeastTwo Real 800 Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 799 (instOfNatNat 799))
                (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 798 (instOfNatNat 798))))))
          p3713)
        (p23595 (p23596 (p23598 (@Eq.refl Bool false)))
          (p23612
            (@p23613
              (@OfNat.ofNat Real 500
                (@instOfNatAtLeastTwo Real 500 Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 499 (instOfNatNat 499))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 498 (instOfNatNat 498))))))
              (@p23614
                (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                  (@OfNat.ofNat Real 32
                    (@instOfNatAtLeastTwo Real 32 Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 31 (instOfNatNat 31))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 30 (instOfNatNat 30))))))
                  Real.pi)
                a)
              (p8412 (@Eq.refl Bool false)))))
        (@Mathlib.Tactic.Linarith.mul_neg Real Real.instRing Real.partialOrder Real.instIsStrictOrderedRing
          p3713
          (@OfNat.ofNat Real 800
            (@instOfNatAtLeastTwo Real 800 Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 799 (instOfNatNat 799))
                (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 798 (instOfNatNat 798))))))
          p3995 (p8414 (@Eq.refl Bool false)))))

noncomputable def p23616 :=
@Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal d64)
  (hardyZApproximantRS
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
      true 5))
  false p22163 p20575

noncomputable def p23617 :=
@Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.fstVal d64) p22163
  p20575 p22165 p20578
  (@p23616 p22165 p20578
    (@Eq.refl Real
      (hardyZApproximantRS
        (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
          true 5)))
    d280)

noncomputable def p23618 :=
@Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal d64)
  (hardyZApproximantRS
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
      true 5))
  true p22812 p20588

noncomputable def p23619 :=
@Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.sndVal d64) p22812
  p20588 p22814 p22175
  (@p23618 p22814 p22175
    (@Eq.refl Real
      (hardyZApproximantRS
        (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
          true 5)))
    d289)

noncomputable def p23620 :=
@Zeta.Certificates.ZIntervalRS.Certificate.mk d64
  (@Eq.mpr p23530 p23532
    (@id (@Eq Prop p23530 p23532)
      (@Eq.trans Prop p23530 p23532 p23532
        (p23534 (p23535 (@Eq.refl Real p4068)))
        (p23538 (p23542 (@Eq.refl Real p4068)))))
    (p23543 p23615))
  (BSN.mul_neg_of_pos_neg_r (Zeta.Certificates.ZIntervalRS.fstVal d64)
    (Zeta.Certificates.ZIntervalRS.sndVal d64)
    (p23617 (Eq.refl true) (Eq.refl true) (Eq.refl true))
    (p23619 (Eq.refl true) (Eq.refl true)
      (Eq.refl true)))

noncomputable def p23621 :=
@Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal d64)
  (hardyZErrorBoundRS (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE d64)))
  false false p22163 p20575 p22165

noncomputable def p23622 :=
@p23621 p20578 5927655089 549755813888 201
  549755813888
  (@p23616 p22165 p20578
    (@Eq.refl Real
      (hardyZApproximantRS
        (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
          true 5)))
    d280)

noncomputable def p23623 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZErrorBoundRS (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE d64)))
  (hardyZErrorBoundRS
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
      true 5))
  false 5927655089 549755813888

noncomputable def p23624 :=
p23622
  (@p23623 201 549755813888
    (@Eq.refl Real
      (hardyZErrorBoundRS
        (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102026600
          true 5)))
    d290)

noncomputable def p23625 :=
@Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal d64)
  (hardyZErrorBoundRS (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE d64)))
  true false p22812 p20588 p22814

noncomputable def p23626 :=
@p23625 p22175 5918727087 549755813888 201
  549755813888
  (@p23618 p22814 p22175
    (@Eq.refl Real
      (hardyZApproximantRS
        (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
          true 5)))
    d289)

noncomputable def p23627 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZErrorBoundRS (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE d64)))
  (hardyZErrorBoundRS
    (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
      true 5))
  false 5918727087 549755813888

noncomputable def p23628 :=
p23626
  (@p23627 201 549755813888
    (@Eq.refl Real
      (hardyZErrorBoundRS
        (@OfScientific.ofScientific Real (@NNRatCast.toOfScientific Real Real.instNNRatCast) 102149700
          true 5)))
    d291)

theorem d292 : Zeta.Certificates.ZIntervalRS.Certificate d64 :=
p23620
  (p23624 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (p23628 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
end RHHeight1000.GramZero664

theorem solution : ∃ t ∈ Set.Ioo (1020.26600 : ℝ) (1021.49700 : ℝ), riemannZeta (1 / 2 + Complex.I * t) = 0 := by
  exact riemannZeta.exists_zero_of_zIntervalRS_certificate _ RHHeight1000.GramZero664.d292
