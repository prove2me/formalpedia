-- Prove2me | solution 1 for RHHeight1000.gram_zero662_exists
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-19T16:40:52.984525+00:00
-- url     : https://prove2.me/submissions/486d0753-dcae-4e11-9b17-bbbdb7eb2b72

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

namespace RHHeight1000.GramZero662
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

noncomputable def p300 :=
@Mathlib.Meta.NormNum.isRat_le_true.{0} Real
  (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField)) Real.linearOrder
  Real.instIsStrictOrderedRing
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
    true 5)
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
    true 5)
  (Int.ofNat 254449) (Int.ofNat 254757) 250

noncomputable def p301 :=
@Mathlib.Meta.NormNum.isNNRat_nnratCast.{0} Real
  (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))
  (@FloorSemiring.instCharZero.{0} Real Real.semiring Real.partialOrder
    (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing))
  (NNRat.divNat 101779600
    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
      (@OfNat.ofNat.{0} Nat 10 (instOfNatNat 10)) 5))
  254449 250

noncomputable def p302 :=
@Mathlib.Meta.NormNum.isNNRat_divNat 101779600 101779600 254449
  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
    (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
    (@OfNat.ofNat.{0} Nat 10 (instOfNatNat 10)) 5)
  100000 250 (Mathlib.Meta.NormNum.IsNat.raw_refl 101779600)

noncomputable def p303 :=
@Mathlib.Meta.NormNum.isNNRat_div.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield)
  (@Nat.cast.{0} NNRat
    (@AddMonoidWithOne.toNatCast.{0} NNRat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat
          (@Semiring.toNonAssocSemiring.{0} NNRat
            (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))))))
    101779600)
  (@Nat.cast.{0} NNRat
    (@AddMonoidWithOne.toNatCast.{0} NNRat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat
          (@Semiring.toNonAssocSemiring.{0} NNRat
            (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))))))
    100000)

noncomputable def p304 :=
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
    101779600)
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

noncomputable def p305 :=
@Mathlib.Meta.NormNum.IsNat.to_isNNRat.{0} NNRat
  (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))
  (@Nat.cast.{0} NNRat
    (@AddMonoidWithOne.toNatCast.{0} NNRat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat
          (@Semiring.toNonAssocSemiring.{0} NNRat
            (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))))))
    101779600)
  101779600

noncomputable def p306 :=
p305
  (@Mathlib.Meta.NormNum.isNat_natCast.{0} NNRat
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat
        (@Semiring.toNonAssocSemiring.{0} NNRat
          (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield)))))
    101779600 101779600 (Mathlib.Meta.NormNum.IsNat.raw_refl 101779600))

noncomputable def p307 :=
@p304 101779600 1 254449 1 100000 250
  400
  (@Eq.refl.{1} (NNRat → NNRat → NNRat)
    (@HMul.hMul.{0, 0, 0} NNRat NNRat NNRat
      (@instHMul.{0} NNRat
        (@Distrib.toMul.{0} NNRat
          (@instDistribOfSemiring.{0} NNRat
            (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield)))))))
  p306 (@p9 1 p11)

noncomputable def p308 :=
@p300 250
  (@Mathlib.Meta.NormNum.IsNNRat.to_isRat.{0} Real
    (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
      true 5)
    254449 250
    (@Mathlib.Meta.NormNum.isNNRat_ofScientific_of_true.{0} Real
      (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)) 101779600
      5 254449 250
      (p301
        (p302 p4
          (@p303 254449 250
            (p307 (@Eq.refl.{1} Nat (Nat.mul 101779600 1))
              (@Eq.refl.{1} Nat 100000)))))))

noncomputable def p309 :=
@Mathlib.Meta.NormNum.isNNRat_nnratCast.{0} Real
  (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))
  (@FloorSemiring.instCharZero.{0} Real Real.semiring Real.partialOrder
    (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing))
  (NNRat.divNat 101902800
    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
      (@OfNat.ofNat.{0} Nat 10 (instOfNatNat 10)) 5))
  254757 250

noncomputable def p310 :=
@Mathlib.Meta.NormNum.isNNRat_divNat 101902800 101902800 254757
  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
    (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
    (@OfNat.ofNat.{0} Nat 10 (instOfNatNat 10)) 5)
  100000 250 (Mathlib.Meta.NormNum.IsNat.raw_refl 101902800)

noncomputable def p311 :=
@Mathlib.Meta.NormNum.isNNRat_div.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield)
  (@Nat.cast.{0} NNRat
    (@AddMonoidWithOne.toNatCast.{0} NNRat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat
          (@Semiring.toNonAssocSemiring.{0} NNRat
            (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))))))
    101902800)
  (@Nat.cast.{0} NNRat
    (@AddMonoidWithOne.toNatCast.{0} NNRat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat
          (@Semiring.toNonAssocSemiring.{0} NNRat
            (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))))))
    100000)

noncomputable def p312 :=
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
    101902800)
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

noncomputable def p313 :=
@Mathlib.Meta.NormNum.IsNat.to_isNNRat.{0} NNRat
  (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))
  (@Nat.cast.{0} NNRat
    (@AddMonoidWithOne.toNatCast.{0} NNRat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat
          (@Semiring.toNonAssocSemiring.{0} NNRat
            (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))))))
    101902800)
  101902800

noncomputable def p314 :=
p313
  (@Mathlib.Meta.NormNum.isNat_natCast.{0} NNRat
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat
        (@Semiring.toNonAssocSemiring.{0} NNRat
          (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield)))))
    101902800 101902800 (Mathlib.Meta.NormNum.IsNat.raw_refl 101902800))

noncomputable def p315 :=
@p312 101902800 1 254757 1 100000 250
  400
  (@Eq.refl.{1} (NNRat → NNRat → NNRat)
    (@HMul.hMul.{0, 0, 0} NNRat NNRat NNRat
      (@instHMul.{0} NNRat
        (@Distrib.toMul.{0} NNRat
          (@instDistribOfSemiring.{0} NNRat
            (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield)))))))
  p314 (@p9 1 p11)

noncomputable def p316 :=
p308
  (@Mathlib.Meta.NormNum.IsNNRat.to_isRat.{0} Real
    (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
      true 5)
    254757 250
    (@Mathlib.Meta.NormNum.isNNRat_ofScientific_of_true.{0} Real
      (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)) 101902800
      5 254757 250
      (p309
        (p310 p4
          (@p311 254757 250
            (p315 (@Eq.refl.{1} Nat (Nat.mul 101902800 1))
              (@Eq.refl.{1} Nat 100000)))))))

theorem d49 : @LE.le.{0} Real
  (@Preorder.toLE.{0} Real
    (@PartialOrder.toPreorder.{0} Real
      (@SemilatticeInf.toPartialOrder.{0} Real
        (@Lattice.toSemilatticeInf.{0} Real
          (@DistribLattice.toLattice.{0} Real (@instDistribLatticeOfLinearOrder.{0} Real Real.linearOrder))))))
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
    true 5)
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
    true 5) :=
p316 (Eq.refl true)

noncomputable def d50 :=
@NonemptyInterval.mk.{0} Real Real.instLE
  (@Prod.mk.{0, 0} Real Real
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
      true 5)
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
      true 5))
  d49

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

noncomputable def p1053 :=
nat_lit 392318858461667547739736838950479151006397215279002157056

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

noncomputable def p2559 :=
nat_lit
  17435272417135788825858293549118708756433572924330842063800398653364207316612315538094101583462747936153803290767102953267003559845146097247846400000000000000000000000000000000000000000000000000000000000000000000000000000

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

noncomputable def p2646 :=
nat_lit
  18384732040517988058098928146181029592990301167271500207433495074180196305072615363872242148647474559264065962695855987953236410770294878979458770736738308867124182908928000

noncomputable def p2649 :=
nat_lit
  2812864002199252172889136006365697527727516078592539531737324746349570034676110150672453048743063607567402092292465966156845170847855116483857191922720961256669999985065984000

noncomputable def p2734 :=
nat_lit 1119872371088902105278721140284222139060822748617324767449994550481895935590080472690438746635803557888

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

noncomputable def p3344 :=
nat_lit 158456325028528675187087900672

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

noncomputable def p5018 :=
nat_lit 73786976294838206464000000000000000

noncomputable def p5240 :=
nat_lit 139984046386112763159840142535527767382602843577165595931249318810236991948760059086304843329475444736

noncomputable def p5581 :=
nat_lit
  57586096570152913699974892898380567793532123114264532903689671329431521032595044740083720782129802971518987656109067457577065805510327036019308994315074097345724416

noncomputable def p8047 :=
nat_lit
  4468076286714625639784492962913075132672523172801071230414488484402368211034852979132858368000000000000000000000000000000000000000000000000000000

noncomputable def p10041 :=
nat_lit 253530120045645880299340641075200000000000000

noncomputable def p10376 :=
nat_lit 401734511064747568885490523085290650630550748445698208825344000000000

noncomputable def p10380 :=
nat_lit 5444517870735015415413993718908291383296000000

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

noncomputable def p12185 :=
nat_lit 475580120650324377600000000

noncomputable def p12189 :=
nat_lit 9903520314283042199192993792

noncomputable def p12205 :=
nat_lit
  724395325779541883127972740267467641917054236400314122627846279324277345529845529720229616430545782367401373900304422017855283570911757419651361948377693681253993101024836647459626987279301240215309090298978493065512302911076452246852449566697292461376960433893740547516518998105653248000

noncomputable def p12208 :=
nat_lit
  110832484844269908118579829260922549213309298169248060762060480736614433866066366047195131313873504702212410206746576568731858386349498885206658378101787133231860944456800007061322929053733089752942290815743709439023382345394697193768424783704685746590674946385742303770027406710164946944000

noncomputable def p12222 :=
nat_lit 121416805764108066932466369176469931665150427440758720078238275608681517825325531136

noncomputable def p12224 :=
nat_lit
  63713936459477097952240406748620611552931532717332212308858141409280000000000000000000000000000000000000000000000000000000000000

noncomputable def p12238 :=
nat_lit 4271974071841820164790043412339104229205409044713305539894083215644439451561281100045924173873152

noncomputable def p12261 :=
nat_lit 24519928653854221733733552434404946937899825954937634816

noncomputable def p12265 :=
nat_lit 4951760157141521099596496896

noncomputable def p12284 :=
nat_lit 696898287454081973172991196020261297061888

noncomputable def p12286 :=
nat_lit 21267647932558653966460912964485513216000000000000000

noncomputable def p12314 :=
nat_lit 348449143727040986586495598010130648530944

noncomputable def p12340 :=
nat_lit 649325391394576216883200000000000000000000000

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

noncomputable def p12383 :=
nat_lit 14834556835581804148908799222814992897429394702737269063680000000000000000000000000000000000000000000000

noncomputable def p12388 :=
nat_lit 431359146674410236714672241392314090778194310760649159697657763987456

noncomputable def p12402 :=
nat_lit 973988087091864325324800000000000000000000000

noncomputable def p12424 :=
nat_lit 3453939416348422912161052046067778230046246830080000000000000000000000000000000

noncomputable def p12427 :=
nat_lit 174224571863520493293247799005065324265472

noncomputable def p12450 :=
nat_lit 1393796574908163946345982392040522594123776

noncomputable def p12453 :=
nat_lit 8366493961506314049878241155481600000000000000000000000000000000000000

noncomputable def p12464 :=
nat_lit 2788831320502104683292747051827200000000000000000000000000000000000000

noncomputable def p12472 :=
nat_lit 35933817946851101741732358544794723129753600000000000000000000000000000000000000000000000000000

noncomputable def p14074 :=
nat_lit 196159429230833773869868419475239575503198607639501078528

noncomputable def p14421 :=
nat_lit 60446290980731458735308800000000000000

noncomputable def p14431 :=
nat_lit 1267650600228229401496703205376

noncomputable def p14476 :=
nat_lit 3064991081731777716716694054300618367237478244367204352

noncomputable def p14484 :=
nat_lit
  3450873173395281893717377931138512726225554486085193277581262111899648000000000000000000000000000000000000000000000

noncomputable def p14489 :=
nat_lit 22835963083295358096932575511191922182123945984000000000000000000000000000000

noncomputable def p14492 :=
nat_lit 151115727451828646838272000000000000000

noncomputable def p14536 :=
nat_lit 324518553658426726783156020576256000000000000000000000000000000

noncomputable def p15591 :=
nat_lit
  8498207885068273579033411304839498037273489883632510771191106211206456957773635883826600036243668570702229271779944016245545269402443315830552319660265397631101300333366291504507650048

noncomputable def p15814 :=
nat_lit 86469112845513523200000000

noncomputable def p15874 :=
nat_lit
  4280528994397723129507835988463142326332233186641591649370616086334967125456923470802661531755578368730858425306122747239013298128334544361442972611807824314368000

noncomputable def p15877 :=
nat_lit
  654920936142851638814698906234860775928831677556163522353704261209249970194909291032807214358603490415821339071836780327569034613635185287300774809606597120098304000

noncomputable def p16688 :=
nat_lit 5178608931694011630164526274146324793284443241682828473139200000000000000000000000000000000000000

noncomputable def p16696 :=
nat_lit 1726202977231337210054842091382108264428147747227609491046400000000000000000000000000000000000000

noncomputable def p16737 :=
nat_lit 2659636803152184184353587200000000

noncomputable def p17677 :=
nat_lit
  19291527220961160051851685871151386369098155571340299021377898009396092446403443984939591663051543749342442495009819444688765754501796740344956911101734995477335766397421086437815836261

noncomputable def p17678 :=
Enclosure.Real.IsNear
  (hardyZApproximantRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
      true 5))
  false p17677 p15591

noncomputable def p17679 :=
nat_lit
  161601819352499345413106966833466597212398525899067651936300480858000609243598803534337115509331563764675430050005057053467335603398879030236131950140363729825452694539542599265526242041340314802379075637887618454622292115815414373717203

noncomputable def p17680 :=
nat_lit
  49401447649430203680546820718272845296783426631793771068921121753957435513958440432005806013935299529648994039439034569124169167488869031310080253072285148002270576640000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p17681 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZApproximantRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
      true 5))
  (hardyZApproximantRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
      true 5))
  false p17677

noncomputable def p17682 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
  (Zeta.RiemannSiegel.mainSumOfPhase
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
      true 5)
    12)

noncomputable def p17683 :=
@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p17684 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (@HPow.hPow.{0, 0, 0} Real Nat Real
    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
    (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)))
    12)
  (p17683
    (@Neg.neg.{0} Real Real.instNeg
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
        (@OfNat.ofNat.{0} Real 4
          (@instOfNatAtLeastTwo.{0} Real 4 Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))))))

noncomputable def p17685 :=
Real.sqrt
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p17686 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p17684
  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
        (Enclosure.sfrac false 12 1)))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Zeta.RiemannSiegel.correctionLinear
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
          (Enclosure.sfrac false 12 1)))
      (@Inv.inv.{0} Real Real.instInv p17685)))

noncomputable def p17687 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZApproximantRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
      true 5))
  (p17682 p17686) false p17677

noncomputable def p17688 :=
@BSN.floor_sqrt_eq_dec
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
    true 5)
  101779600 100000 12
  (Enclosure.sfrac_ofScientific_eq 101779600 5 100000 (Eq.refl true))

noncomputable def p17689 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (Zeta.RiemannSiegel.mainSumOfPhase
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
      true 5)
    12)

noncomputable def p17690 :=
nat_lit
  1138316556826355049739330281819910247076584265780202038579939744564564845901604537086451312241486168803271816798892514552327508170529622839034813125607928177993680257295536716432318875

noncomputable def p17691 :=
nat_lit
  4418903551948288458909246552255504283230406655540406567878101762729068667006932851190628034090766093554274196166833344588520951228093386291638059782388652469932694539542599265526242041340314802379075637887618454622292115815414373717203

noncomputable def p17692 :=
nat_lit
  1325703656062751169742794480944967589125388211085228466938862028921275484279926795793335403654410111451824192333245083420850077027039708368335899067378098150941840414208308879859330470590174724096

noncomputable def p17693 :=
@p17689 p17686 165202851377 68719476736 27331
  8589934592 p17690 p15591 p17691
  p17680 p17692 p17677

noncomputable def p17694 :=
@Enclosure.Real.IsNear.of_eq
  (Zeta.RiemannSiegel.mainSumOfPhase
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
      true 5)
    12)

noncomputable def p17695 :=
@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
      true 5)
    12)

noncomputable def p17696 :=
p17695
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
      true 5)
    12)

noncomputable def p17697 :=
@p17694 p17696 false 165202851377 68719476736
  27331 8589934592
  (BSN.main_sum_of_phase_eq
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
      true 5)
    12)

noncomputable def p17698 :=
@Enclosure.Real.IsNear.addLit_ff
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
      true 5)
    12)

noncomputable def p17699 :=
@p17698
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
      true 5)
    12)

noncomputable def p17700 :=
@p17699 165202851377 137438953472 218648 137438953472
  165202851377 137438953472 218648 137438953472
  45410614007690468261888 165202851377 68719476736

noncomputable def p17701 :=
BSN.mainSumRS_step
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
      true 5))
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
    true 5)
  Real.cos BSN.quadSignNeg

noncomputable def p17702 :=
p17701 11 12 101779600 100000 286
  137438953472 68719476736 2305843009213693952 false 285836864804428
  3372

noncomputable def p17703 :=
p17702 341522969406 43 39675208392 8 false
  204470905639 205030 true 19706829228 7244019458077122842 1

noncomputable def p17704 :=
p17703 false 136028530190 true false 165202851377 218648
  BSN.abs_quadSignNeg (BSN.cos_quad_nat2 286 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 136028530190 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101779600 5 100000 (Eq.refl true))
  (Eq.refl true)

noncomputable def p17705 :=
BSN.mainSumRS_step2
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
      true 5))
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
    true 5)
  Real.sin Real.sin

noncomputable def p17706 :=
p17705 BSN.quadSignPos BSN.quadSignNeg 9 10 11 101779600
  100000 167 229 137438953472 68719476736

noncomputable def p17707 :=
p17706 2305843009213693952 false 285836864804428 3372
  316464885454 43 43462013224 8 329564216814 43
  41439403656

noncomputable def p17708 :=
p17707 8 false 198392271595 175892 true 206433004628
  true 153786662625 7244019458077122842 1 false

noncomputable def p17709 :=
p17708 137113816081 false false 123645635169 true false
  204470905639 205030 BSN.abs_quadSignPos
  (BSN.cos_quad_nat3 167 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 137113816081 137438953472)

noncomputable def p17710 :=
p17705 BSN.quadSignPos BSN.quadSignPos 7 8 9 101779600
  100000 23 99 137438953472 68719476736

noncomputable def p17711 :=
p17710 2305843009213693952 false 285836864804428 3372
  285796269294 43 48592008000 16 301984246446 43
  45812984488

noncomputable def p17712 :=
p17711 8 false 131260362412 143487 true 79997022663
  true 148521567362 7244019458077122842 1 false

noncomputable def p17713 :=
p17712 75555919006 false false 121256573524 false false
  198392271595 175892 BSN.abs_quadSignPos
  (BSN.cos_quad_nat3 23 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 75555919006 137438953472)

noncomputable def p17714 :=
p17705 BSN.quadSignPos BSN.quadSignPos 5 6 7 101779600
  100000 163 63 137438953472 68719476736

noncomputable def p17715 :=
p17714 2305843009213693952 false 285836864804428 3372
  246257546308 43 56109217800 8 267443854420 43
  51947041624

noncomputable def p17716 :=
p17715 8 false 116166994900 106407 false 7076868937
  false 32597545011 7244019458077122842 1 false

noncomputable def p17717 :=
p17716 7073742174 false false 32292782081 false false
  131260362412 143487 BSN.abs_quadSignPos
  (BSN.cos_quad_nat3 163 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 7073742174 137438953472)

noncomputable def p17718 :=
p17705 BSN.quadSignNeg BSN.quadSignNeg 3 4 5 101779600
  100000 425 281 137438953472 68719476736

noncomputable def p17719 :=
p17718 2305843009213693952 false 285836864804428 3372
  190530846192 42 68719476728 8 221199462352 42
  61464568544

noncomputable def p17720 :=
p17719 16 false 195819305433 62694 false
  162675282845 false 36239300880 7244019458077122842 1 false

noncomputable def p17721 :=
p17720 127265491056 true false 35820836337 true false
  116166994900 106407 BSN.abs_quadSignNeg
  (BSN.cos_quad_nat1 425 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 127265491056 137438953472)

noncomputable def p17722 :=
BSN.mainSumRS_step2
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
      true 5))
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
    true 5)
  Real.cos Real.cos

noncomputable def p17723 :=
p17722 BSN.quadSignNeg BSN.quadSignPos 1 2 3 101779600
  100000 874 612 137438953472 68719476736

noncomputable def p17724 :=
p17723 2305843009213693952 false 285836864804428 3372
  95265423088 42 97184016000 16 150992123216 42
  79350416784

noncomputable def p17725 :=
p17724 16 false 137438497384 3418 false 189458987118
  false 33860560996 7244019458077122842 1 false

noncomputable def p17726 :=
p17725 26267024368 true false 133288929110 false false
  195819305433 62694 BSN.abs_quadSignNeg
  (BSN.cos_quad_nat2 874 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 26267024368 137438953472)

noncomputable def p17727 :=
@Enclosure.Real.IsNear.recentre'
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
      true 5)
    1)

noncomputable def p17728 :=
@Enclosure.Real.IsNear.of_eq
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
      true 5)
    1)

noncomputable def p17729 :=
@p17728
  (Real.cos
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
        true 5)))
  false 17179812173

noncomputable def p17730 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
        true 5)))
  false 17179812173

noncomputable def p17731 :=
@Enclosure.Real.IsNear.cos_image
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
      true 5))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 35729608100553)
    (@Nat.cast.{0} Real Real.instNatCast 17179869184))
  false 35729608100553

noncomputable def p17732 :=
nat_lit 2859733098775933692363978448192657390037119217748318707

noncomputable def p17733 :=
nat_lit 1375045603631022046325086229869428090585332318208000

noncomputable def p17734 :=
@Enclosure.Real.IsNear.recentre'
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
      true 5))
  false p17732 p17733

noncomputable def p17735 :=
nat_lit 5767168000000000000000000

noncomputable def p17736 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 101779600 400000)
      (Real.log (Enclosure.sfrac false 41436357904640000 160000000000)))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 1 4)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 1 2) Real.pi)
        (Real.arctan
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@Nat.cast.{0} Real Real.instNatCast 100000)
            (@Nat.cast.{0} Real Real.instNatCast 203559200))))))

noncomputable def p17737 :=
nat_lit 524258163211452243079963831828480000000000000000

noncomputable def p17738 :=
nat_lit 3201527529468345563684325269119413780480000000000000

noncomputable def p17739 :=
@Enclosure.Real.IsNear.of_eq
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
      true 5))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (p17736 (Enclosure.sfrac false 101779600 200000))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 101779600 200000) (Real.log Real.pi)))
    (Enclosure.sfrac true p17737 p17738))
  false

noncomputable def p17740 :=
BSN.riemannSiegelThetaApproximant_two_zero_mk
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
    true 5)
  101779600 100000 41436357904640000 160000000000

noncomputable def p17741 :=
p17740 203559200 400000 200000 p17737
  p17738
  (Enclosure.sfrac_ofScientific_eq 101779600 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p17742 :=
@Enclosure.Real.IsNear.addLit_ft_p
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (p17736 (Enclosure.sfrac false 101779600 200000))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 101779600 200000) (Real.log Real.pi)))
  (Enclosure.sfrac true p17737 p17738) 9366303123387241204359
  4503599627370496000

noncomputable def p17743 :=
nat_lit 29986474937820734474042510652920639154155623208696610365112320000000000000

noncomputable def p17744 :=
@p17742 141463925852722719 p17735 p17737
  p17738 0 1 p17743 p17732
  p17733 141463925852722719 p17735

noncomputable def p17745 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (p17736 (Enclosure.sfrac false 101779600 200000))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 101779600 200000) (Real.log Real.pi))
  11989878461509036018311 4503599627370496000 53450666669 5500000000000000000

noncomputable def p17746 :=
nat_lit 321823724794966829731084461146112000

noncomputable def p17747 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 101779600 400000)
      (Real.log (Enclosure.sfrac false 41436357904640000 160000000000)))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 1 4)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 1 2) Real.pi)
        (Real.arctan
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@Nat.cast.{0} Real Real.instNatCast 100000)
            (@Nat.cast.{0} Real Real.instNatCast 203559200))))))

noncomputable def p17748 :=
@p17747 (Enclosure.sfrac false 101779600 200000)
  14281751304678626691719 4503599627370496000 53450666669 5500000000000000000
  101779600 200000 0

noncomputable def p17749 :=
nat_lit 2397975692301807203662200000

noncomputable def p17750 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 101779600 400000)
    (Real.log (Enclosure.sfrac false 41436357904640000 160000000000)))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 1 4)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 1 2) Real.pi)
      (Real.arctan
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@Nat.cast.{0} Real Real.instNatCast 100000)
          (@Nat.cast.{0} Real Real.instNatCast 203559200)))))
  14283519311009833161719

noncomputable def p17751 :=
nat_lit 32159644926974379127538072431794061312

noncomputable def p17752 :=
@p17750 4503599627370496000 318203995889 33000000000000000000
  884003165603235 2251799813685248 20000033 264000000000000000
  p17751 14281751304678626691719 4503599627370496000 53450666669

noncomputable def p17753 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 101779600 400000)
  (Real.log (Enclosure.sfrac false 41436357904640000 160000000000)) 101779600
  400000 0 1 56135097056816231 4503599627370496

noncomputable def p17754 :=
nat_lit 30860595970151880451453616128

noncomputable def p17755 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast 41436357904640000)
      (@Nat.cast.{0} Real Real.instNatCast 160000000000)))
  false p17754 p2333

noncomputable def p17756 :=
BSN.log_rat_reduce_isNear 41436357904640000 160000000000 17 82872715809280000
  41943040000000000 46797508658 68719476736 24973259072661432
  36028797018963968 26400000000 1000000000000000

noncomputable def p17757 :=
nat_lit
  989181290148254774678915870764911934615745102268707494350563387767404147539133446583887469138423132154003869126506604217075498051527955061007444489501514627378866969399631668385752081355682359402133015675999441171419953862833566413244956564452747919059907231616885185772463210722750046928896000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p17758 :=
nat_lit
  37935652720701949215063939210429218662531887099225812374593167054318474671401238674427784975551733554410832701206549640211963078691190818706237641735600576894934772765638617071249010637631794647795098377665230987655102142268882617146479460530326960786652751896054932762370075704725358614937600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p17759 :=
nat_lit
  956012832998761059122830696985282949222309558814987094205548576953564343433393003568733400331798778782136135265071361733348693719534780388427361981644449523643950389719090785445493680805996017055818556235572010996670524181595347780867716321841089411547058994654943758276678909952000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p17760 :=
BSN.log_dyadic_bound 20464837904640000 62407877904640000 12 11
  p17757 68719476736 26400000000 p17758 p17759
  46797508658 82872715809280000

noncomputable def p17761 :=
p17760 41943040000000000 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p17762 :=
@BSN.binarySplit_of_base11 (BSN.artanhP 20464837904640000) (BSN.artanhQ 62407877904640000)
  0 11 p17758 p17757 p17759
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p17763 :=
p17756 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p17761 (p17762 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

noncomputable def p17764 :=
@p17753 1250561 33000000000000000 14283519311009833161719
  4503599627370496000 318203995889 33000000000000000000
  (Enclosure.Real.IsNear.const false 101779600 400000)
  (BSN.isNear_log_sfrac 41436357904640000 160000000000 56135097056816231
    4503599627370496 1250561 33000000000000000 false
    (@p17755 1000448800000000 p2422 56135097056816231
      4503599627370496 1250561 33000000000000000
      (p17763 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p17765 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 1 4)
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 1 2) Real.pi)
    (Real.arctan
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@Nat.cast.{0} Real Real.instNatCast 100000)
        (@Nat.cast.{0} Real Real.instNatCast 203559200))))
  1 4

noncomputable def p17766 :=
@p17765 0 1 884003165603235 562949953421312 20000033
  66000000000000000 884003165603235 2251799813685248 20000033
  264000000000000000 (Enclosure.Real.IsNear.const false 1 4)

noncomputable def p17767 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 1 2) Real.pi)
  (Real.arctan
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast 100000) (@Nat.cast.{0} Real Real.instNatCast 203559200)))
  884279719003555 562949953421312 1

noncomputable def p17768 :=
nat_lit 7593529371652732873605120

noncomputable def p17769 :=
@p17767 2000000000000000 4219870 8589934592 1
  3300000000 p17768 884003165603235 562949953421312 20000033
  66000000000000000
  (@p803 1 1000000000000000 884279719003555 562949953421312
    1 2000000000000000 (Enclosure.Real.IsNear.const false 1 2)
    BSN.pi_near_15 (Eq.refl true))

noncomputable def p17770 :=
BSN.arctan_dyadic_bound_f 100000 203559200 1 0 8589934592
  3300000000 0 1 1 0 1

noncomputable def p17771 :=
p17770 1 4219870 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)
  (@BSN.binarySplit_of_le (BSN.arctanEvenP 100000) (BSN.arctanEvenQ 203559200) 0
    0 (Eq.refl true))
  (@BSN.binarySplit_of_le (BSN.arctanOddP 100000) (BSN.arctanOddQ 203559200) 0 0
    (Eq.refl true))

noncomputable def p17772 :=
p17766
  (p17769
    (p17771 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p17773 :=
@p17745 20016291336988791 34359738368000 254449 17179869184000
  p17746 9366303123387241204359 4503599627370496000 141463925852722719
  p17735
  (@p17748 1 p17749 11989878461509036018311
    4503599627370496000 53450666669 5500000000000000000
    (@p17752 5500000000000000000 p17764 p17772
      (Eq.refl true) (Eq.refl true))
    (Enclosure.Real.IsNear.const false 101779600 200000) (Eq.refl true)
    (Eq.refl true))

noncomputable def p17774 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 101779600 200000) (Real.log Real.pi)
  101779600 200000 0 1 78665238759 68719476736

noncomputable def p17775 :=
p17773
  (@p17774 1 34359738368 20016291336988791 34359738368000
    254449 17179869184000
    (Enclosure.Real.IsNear.const false 101779600 200000) d91
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p17776 :=
@p17731 17179869184 211 8589934592 false 17179812173
  17179869184 1 3300000000
  (@p17734 141463925852722719 p17735 35729608100553
    17179869184 211 8589934592
    (@p17739 p17732 p17733 141463925852722719
      p17735
      (p17741 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p17744 (p17775 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p17737 p17738)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p17777 :=
nat_lit 6378391038702666892967936

noncomputable def p17778 :=
BSN.cos_reduce0
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 35729608100553)
    (@Nat.cast.{0} Real Real.instNatCast 17179869184))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast p17777)
    (@Nat.cast.{0} Real Real.instNatCast p2333))
  226375608064910080 72057594037927936 false

noncomputable def p17779 :=
BSN.sin_reduce_arg_pos_rat_q0 35729608100553 17179869184 226375608064910080
  72057594037927936 331 p17777 p2333
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p17780 :=
BSN.cos_dyadic_bound_f 90642388367 35184372088832 1 0 17179869184
  6606445313 0 1 1 0 1

noncomputable def p17781 :=
p17780 1 17179812173 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (@BSN.binarySplit_of_le (BSN.cosEvenP 90642388367) (BSN.cosEvenQ 35184372088832) 0
    0 (Eq.refl true))

noncomputable def p17782 :=
p17781
  (@BSN.binarySplit_of_le (BSN.cosOddP 90642388367) (BSN.cosOddQ 35184372088832) 0
    0 (Eq.refl true))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p17783 :=
@BSN.cos_arg_round false 17179812173 17179869184 p17777
  p2333 90642388367 35184372088832 6606445313 6600000000
  p17782 (Eq.refl true)

noncomputable def p17784 :=
p17778 17179812173 17179869184 331 1000000000000000
  6600000000 3300000000 p17779 BSN.pi_near_15 p17783
  (Eq.refl true) (Eq.refl true)

noncomputable def p17785 :=
@p17729 17179869184 2753476307 110729625600000000
  (BSN.main_sum_rs_one
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
      true 5))
  (@p17730 17179869184 704889934592 28346784153600000000
    17179812173 17179869184 2753476307 110729625600000000
    (p17776 (Enclosure.sfrac_false_div 35729608100553 17179869184)
      (p17784 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p17786 :=
@p17727 false 17179812173 17179869184 2753476307
  110729625600000000 137438497384 137438953472 3418 137438953472
  p17785 (Eq.refl true)

noncomputable def p17787 :=
p17726 BSN.abs_quadSignPos (BSN.cos_quad_nat0 612 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 133288929110 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101779600 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true) p17786
  (@p17734 141463925852722719 p17735 285836864804428
    137438953472 3372 137438953472
    (@p17739 p17732 p17733 141463925852722719
      p17735
      (p17741 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p17744 (p17775 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p17737 p17738)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p17788 :=
nat_lit
  51135206562252662996616225254552915233032136521120014197817402290656037807557678460827694731594060538111928649056634270202625060985703743053359804606750547030343624486708915452897202714771456

noncomputable def p17789 :=
nat_lit
  2755772605088545438845347493660621043785228795524865858940137592096656322512174168257306189926653522956689225414965967969260897225757990089160924569901437672866415822874501122686976

noncomputable def p17790 :=
nat_lit
  520833046961210335781702431432669368088637957494487735747358410406058243878226693666049757376073604793084744252211835726514277063031478929112722794602583582396264117769179429215646976196018176

noncomputable def p17791 :=
BSN.cos_dyadic_bound_f 189458987118 137438953472 5 4 137438953472
  68719476736 p17788 p2495 p17789
  p17790 p2498

noncomputable def p17792 :=
@BSN.binarySplit_of_base4 (BSN.cosEvenP 189458987118) (BSN.cosEvenQ 137438953472) 0
  4 p17788 p2495 p17789 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p17793 :=
p17791 p17789 26267024368 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p17792 (Eq.refl true))

noncomputable def p17794 :=
@BSN.binarySplit_of_base4 (BSN.cosOddP 189458987118) (BSN.cosOddQ 137438953472) 0
  4 p17790 p2498 p17789 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p17795 :=
nat_lit 787999948264241408283262804299374282869836582807732494888573841822933317992284591992406016

noncomputable def p17796 :=
nat_lit 1728037620806671145053636711233774155912020437188157615994143504837198355046596673536

noncomputable def p17797 :=
nat_lit 2363996388717482611507498305624700381061197924382323108350489537181790279580143682783870976

noncomputable def p17798 :=
BSN.cos_dyadic_bound_f 33860560996 137438953472 3 2 137438953472
  68719476736 p17795 p2466 p17796
  p17797 p2469

noncomputable def p17799 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP 33860560996) (BSN.cosEvenQ 137438953472) 0
  2 p17795 p2466 p17796 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p17800 :=
p17798 p17796 133288929110 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p17799 (Eq.refl true))

noncomputable def p17801 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP 33860560996) (BSN.cosOddQ 137438953472) 0
  2 p17797 p2469 p17796 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p17802 :=
p17787 d93 d95 d97 d99 d103
  (p17793 (p17794 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p17800 (p17801 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p17803 :=
p17721 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 281 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 35820836337 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101779600 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p17802 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p17734 141463925852722719 p17735 285836864804428
    137438953472 3372 137438953472
    (@p17739 p17732 p17733 141463925852722719
      p17735
      (p17741 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p17744 (p17775 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p17737 p17738)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p17804 :=
nat_lit
  4629625698985372974360717842356211462493114644082262505340765900515105750846498130783769603126651526169337058102164831266822291621389411040625

noncomputable def p17805 :=
nat_lit
  343446303324436113091553567620308175155878951349198208521546420822583740904607758056094673652896574561264896009530725412669570556640625

noncomputable def p17806 :=
nat_lit
  23138845679511048466733436729600645927063920421925698908079631970506084493009705945926783546478926636399961792156950120856435336838200828640625

noncomputable def p17807 :=
BSN.sin_dyadic_bound_f 162675282845 137438953472 4 3 137438953472
  68719476736 p17804 p2504 p17805
  p17806 p2507

noncomputable def p17808 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 162675282845) (BSN.sinEvenQ 137438953472) 0
  3 p17804 p2504 p17805 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p17809 :=
p17807 p17805 127265491056 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p17808 (Eq.refl true))

noncomputable def p17810 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 162675282845) (BSN.sinOddQ 137438953472) 0
  3 p17806 p2507 p17805 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p17811 :=
nat_lit 1860977328821630739638873067118978298531219324693493269089004930893782902658291298467840000

noncomputable def p17812 :=
nat_lit 2974667895064521826992357798478320365898809109631464846609638842666539653529600000000

noncomputable def p17813 :=
nat_lit 4873983426022917070780757188160888483634505823744400110956689831973209951612276257587200000

noncomputable def p17814 :=
BSN.sin_dyadic_bound_f 36239300880 137438953472 3 2 137438953472
  68719476736 p17811 p2477 p17812
  p17813 p2480

noncomputable def p17815 :=
@BSN.binarySplit_of_base2 (BSN.sinEvenP 36239300880) (BSN.sinEvenQ 137438953472) 0
  2 p17811 p2477 p17812 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p17816 :=
p17814 p17812 35820836337 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p17815 (Eq.refl true))

noncomputable def p17817 :=
@BSN.binarySplit_of_base2 (BSN.sinOddP 36239300880) (BSN.sinOddQ 137438953472) 0
  2 p17813 p2480 p17812 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p17818 :=
p17803 d105 d107 d109 d111 d103
  (p17809 (p17810 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p17816 (p17817 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p17819 :=
p17717 BSN.abs_quadSignPos (BSN.cos_quad_nat3 63 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 32292782081 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101779600 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p17818 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p17734 141463925852722719 p17735 285836864804428
    137438953472 3372 137438953472
    (@p17739 p17732 p17733 141463925852722719
      p17735
      (p17741 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p17744 (p17775 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p17737 p17738)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p17820 :=
nat_lit 2508214131281061801265017544768618380961

noncomputable def p17821 :=
BSN.sin_dyadic_bound_f 7076868937 137438953472 2 1 137438953472
  68719476736 p17820 p3178 p17820
  p17820 p3179

noncomputable def p17822 :=
@BSN.binarySplit_of_base (BSN.sinEvenP 7076868937) (BSN.sinEvenQ 137438953472) 0
  1 p17820 p3178 p17820 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p17823 :=
p17821 p17820 7073742174 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p17822 (Eq.refl true))

noncomputable def p17824 :=
@BSN.binarySplit_of_base (BSN.sinOddP 7076868937) (BSN.sinOddQ 137438953472) 0 1
  p17820 p3179 p17820 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p17825 :=
nat_lit 1218319440650757910509863292815434149649587048578372299860853225203774369204054146494858785

noncomputable def p17826 :=
nat_lit 1274908889803008899232925807892858633909175629628002631177418257460281434677675918881

noncomputable def p17827 :=
nat_lit 3190834566137591989320947961208162374930177845706622340012260350189849364602580905535047201

noncomputable def p17828 :=
BSN.sin_dyadic_bound_f 32597545011 137438953472 3 2 137438953472
  68719476736 p17825 p2477 p17826
  p17827 p2480

noncomputable def p17829 :=
@BSN.binarySplit_of_base2 (BSN.sinEvenP 32597545011) (BSN.sinEvenQ 137438953472) 0
  2 p17825 p2477 p17826 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p17830 :=
p17828 p17826 32292782081 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p17829 (Eq.refl true))

noncomputable def p17831 :=
@BSN.binarySplit_of_base2 (BSN.sinOddP 32597545011) (BSN.sinOddQ 137438953472) 0
  2 p17827 p2480 p17826 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p17832 :=
p17819 d113 d115 d117 d119 d103
  (p17823 (p17824 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p17830 (p17831 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p17833 :=
p17713 BSN.abs_quadSignPos (BSN.cos_quad_nat3 99 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 121256573524 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101779600 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p17832 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p17734 141463925852722719 p17735 285836864804428
    137438953472 3372 137438953472
    (@p17739 p17732 p17733 141463925852722719
      p17735
      (p17741 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p17744 (p17775 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p17737 p17738)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p17834 :=
nat_lit 44190907811372178960956312417806840434806488159453549537737030333569861755024048106153818305

noncomputable def p17835 :=
nat_lit 1677222150801594275979636247246674270208960265184708997618602153106556454914799469181121

noncomputable def p17836 :=
nat_lit 115735376384397266126057803587950944618531892577187092593791315993958893981278835364595611841

noncomputable def p17837 :=
BSN.sin_dyadic_bound_f 79997022663 137438953472 3 2 137438953472
  68719476736 p17834 p2477 p17835
  p17836 p2480

noncomputable def p17838 :=
@BSN.binarySplit_of_base2 (BSN.sinEvenP 79997022663) (BSN.sinEvenQ 137438953472) 0
  2 p17834 p2477 p17835 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p17839 :=
p17837 p17835 75555919006 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p17838 (Eq.refl true))

noncomputable def p17840 :=
@BSN.binarySplit_of_base2 (BSN.sinOddP 79997022663) (BSN.sinOddQ 137438953472) 0
  2 p17836 p2480 p17835 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p17841 :=
nat_lit
  3216115981609919612173136551881207903916232033078582538885520775502702174240982592595472783934124280810117245694213691636876170698824283590656

noncomputable def p17842 :=
nat_lit
  115205784265662024156670717297385685744957413175408582295480668427612060895438348106843400416881230873716760986359160357953764731129856

noncomputable def p17843 :=
nat_lit
  16076098611075774815164319427533740997276575708383204011006714124613999879552428927432325548447558842079750640350505317057284501369190450466816

noncomputable def p17844 :=
BSN.sin_dyadic_bound_f 148521567362 137438953472 4 3 137438953472
  68719476736 p17841 p2504 p17842
  p17843 p2507

noncomputable def p17845 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 148521567362) (BSN.sinEvenQ 137438953472) 0
  3 p17841 p2504 p17842 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p17846 :=
p17844 p17842 121256573524 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p17845 (Eq.refl true))

noncomputable def p17847 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 148521567362) (BSN.sinOddQ 137438953472) 0
  3 p17843 p2507 p17842 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p17848 :=
p17833 d121 d123 d125 d127 d103
  (p17839 (p17840 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p17846 (p17847 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p17849 :=
p17709 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 229 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 123645635169 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101779600 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p17848 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p17734 141463925852722719 p17735 285836864804428
    137438953472 3372 137438953472
    (@p17739 p17732 p17733 141463925852722719
      p17735
      (p17741 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p17744 (p17775 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p17737 p17738)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p17850 :=
nat_lit
  12017796909119591595402797595450474799435248218491441256370789531486841535043311342744985120158356123177590007454895768708570979416860646178816

noncomputable def p17851 :=
nat_lit
  5988935076506180976890922275971823571604276736855279358190401811456076403941369453995265686840975971264641641529364122921830595549986816

noncomputable def p17852 :=
nat_lit
  60026547462606661949473076918138732391102768909969796695113597820949319360426362364493968403537481955908579677187628445804048420764677807538176

noncomputable def p17853 :=
BSN.sin_dyadic_bound_f 206433004628 137438953472 4 3 137438953472
  68719476736 p17850 p2504 p17851
  p17852 p2507

noncomputable def p17854 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 206433004628) (BSN.sinEvenQ 137438953472) 0
  3 p17850 p2504 p17851 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p17855 :=
p17853 p17851 137113816081 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p17854 (Eq.refl true))

noncomputable def p17856 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 206433004628) (BSN.sinOddQ 137438953472) 0
  3 p17852 p2507 p17851 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p17857 :=
nat_lit
  3697239383092980466988744002705929253063220742236615605298640793155774488047275774993160951901287295318256099591168751727264116735074462890625

noncomputable def p17858 :=
nat_lit
  174994366230987820400465498588778310794371121698106692342648674569698649405116706341161418138932450995289540165686048567295074462890625

noncomputable def p17859 :=
nat_lit
  18480275253787660788635963055292644163031692553460477717564565744904350661603953015999786203729794849760700641959810455892126314495074462890625

noncomputable def p17860 :=
BSN.sin_dyadic_bound_f 153786662625 137438953472 4 3 137438953472
  68719476736 p17857 p2504 p17858
  p17859 p2507

noncomputable def p17861 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 153786662625) (BSN.sinEvenQ 137438953472) 0
  3 p17857 p2504 p17858 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p17862 :=
p17860 p17858 123645635169 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p17861 (Eq.refl true))

noncomputable def p17863 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 153786662625) (BSN.sinOddQ 137438953472) 0
  3 p17859 p2507 p17858 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p17864 :=
p17849 d129 d131 d133 d135 d103
  (p17855 (p17856 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p17862 (p17863 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p17865 :=
p17704
  (p17864 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p17734 141463925852722719 p17735 285836864804428
    137438953472 3372 137438953472
    (@p17739 p17732 p17733 141463925852722719
      p17735
      (p17741 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p17744 (p17775 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p17737 p17738)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p17866 :=
nat_lit 90409852757526429289594172552206735250918026175464350829288593003828051488299964149334016

noncomputable def p17867 :=
nat_lit 22747518419331063329903945480486683454081247360098109781987258263447877409570881536

noncomputable def p17868 :=
nat_lit 271229512777542449206655857848729244779387170363898332291646215036967627569145073306238976

noncomputable def p17869 :=
BSN.cos_dyadic_bound_f 19706829228 137438953472 3 2 137438953472
  68719476736 p17866 p2466 p17867
  p17868 p2469

noncomputable def p17870 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP 19706829228) (BSN.cosEvenQ 137438953472) 0
  2 p17866 p2466 p17867 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p17871 :=
p17869 p17867 136028530190 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p17870 (Eq.refl true))

noncomputable def p17872 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP 19706829228) (BSN.cosOddQ 137438953472) 0
  2 p17868 p2469 p17867 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p17873 :=
p17865 d137 d139 d103
  (p17871 (p17872 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true) (Eq.refl true)

noncomputable def p17874 :=
@p17693 p15591 p17679 p17680
  (p17697
    (@p17700 27331 8589934592
      (p17873 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (p17873 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true) (Eq.refl true)))

noncomputable def p17875 :=
@Enclosure.Real.IsNear.mulLit_ff p17684
  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
        (Enclosure.sfrac false 12 1)))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Zeta.RiemannSiegel.correctionLinear
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
          (Enclosure.sfrac false 12 1)))
      (@Inv.inv.{0} Real Real.instInv p17685)))

noncomputable def p17876 :=
nat_lit
  472762927937483172389688615224993908931615976592118103615264016869439722051838320747268256006844670680388311096819691609149072714849854149913325029102262476188124412960961095

noncomputable def p17877 :=
nat_lit
  989321605892418136242010084078588760140525396404847359656252224371588900426127468681265604244972179958390685704064557357405460137227004839870184620407572671666427088594796544

noncomputable def p17878 :=
nat_lit
  1834107128529779036449143600834891006544155274914333448178000425213641104715775848506386337271338814707129456702510018840214828821851342895858569973570077457980154417569530148245039696273573554381409115465354607570143279718153

noncomputable def p17879 :=
nat_lit
  5751085426824889574263573242150345502512462743533981389938984270435459389579300818965514890609227531781535833077392839957513982370596964763253956692326481920000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p17880 :=
@p17875 2407795725 8589934592 1 8589934592
  p17876 p17877 p17878 p17879
  p17690 p15591 p17691

noncomputable def p17881 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HPow.hPow.{0, 0, 0} Real Nat Real
    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
    (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)))
    12)
  (p17683
    (@Neg.neg.{0} Real Real.instNeg
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
        (@OfNat.ofNat.{0} Real 4
          (@instOfNatAtLeastTwo.{0} Real 4 Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))))))

noncomputable def p17882 :=
@p17881 1 1 0 1 2407795725 8589934592
  1 8589934592 2407795725 8589934592 1

noncomputable def p17883 :=
@Enclosure.Real.IsNear.of_eq
  (p17683
    (@Neg.neg.{0} Real Real.instNeg
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
        (@OfNat.ofNat.{0} Real 4
          (@instOfNatAtLeastTwo.{0} Real 4 Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))))))

noncomputable def p17884 :=
BSN.rpow_neg_quarter_mk
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p17885 :=
p17884
  (BSN.t_div_two_pi_nonneg
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
      true 5)
    101779600 100000
    (Enclosure.sfrac_ofScientific_eq 101779600 5 100000 (Eq.refl true)))

noncomputable def p17886 :=
@Enclosure.Real.IsNear.recentre' (@Inv.inv.{0} Real Real.instInv (Real.sqrt p17685)) false
  4815591450 17179869184 2 17179869184 2407795725 8589934592

noncomputable def p17887 :=
@Enclosure.Real.IsNear.recentre' (Real.sqrt p17685) false 61290063379
  17179869184 7 17179869184 61290063379 17179869184 7
  17179869184

noncomputable def p17888 :=
@Enclosure.Real.IsNear.sqrt_image
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p17889 :=
@Enclosure.Real.IsNear.of_eq
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p17890 :=
@p17889
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 101779600 100000)
    (@Inv.inv.{0} Real Real.instInv
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)))
  false 695730003397247

noncomputable def p17891 :=
@p17890 4294967296000 254449 4294967296000
  (BSN.t_div_two_pi_mk
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
      true 5)
    101779600 100000
    (Enclosure.sfrac_ofScientific_eq 101779600 5 100000 (Eq.refl true)))

noncomputable def p17892 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 101779600 100000)
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi))
  101779600 100000 0

noncomputable def p17893 :=
@p17892 1 2734261103 17179869184 1 17179869184
  695730003397247 4294967296000 254449 4294967296000
  (Enclosure.Real.IsNear.const false 101779600 100000) d142

noncomputable def p17894 :=
@p17888 695730003397247 4294967296000 254449 4294967296000
  109327720370 109327720411 8589934592
  (p17891 (p17893 (Eq.refl true))) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p17895 :=
@Enclosure.Real.IsNear.recentre' p17685 false 218655440781 17179869184
  41 17179869184 218655440781 17179869184 41 17179869184
  (p17894 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p17896 :=
@Enclosure.Real.IsNear.sqrt_image p17685 218655440781 17179869184 41
  17179869184 30645031686 30645031693 8589934592
  (p17895 (Eq.refl true)) (Eq.refl true) (Eq.refl true)

noncomputable def p17897 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt p17685) 61290063379 17179869184
  7 17179869184 2407795724 2407795726 8589934592
  (p17887
    (p17896 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p17898 :=
@p17883 (@Inv.inv.{0} Real Real.instInv (Real.sqrt p17685)) false
  2407795725 8589934592 1 8589934592 p17885
  (@p17886 1 8589934592
    (p17897 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p17899 :=
@Enclosure.Real.IsNear.addLit_ft_p
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
      (Enclosure.sfrac false 12 1)))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Zeta.RiemannSiegel.correctionLinear
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
        (Enclosure.sfrac false 12 1)))
    (@Inv.inv.{0} Real Real.instInv p17685))
  8829732251980597155

noncomputable def p17900 :=
nat_lit
  786488492018253609095292445773760323134209568224973094502770342747262168695223502741795729087594566520520686377379261179120982732128151288477929146202228935934539952426425

noncomputable def p17901 :=
nat_lit
  7077518544963274060233643120110689140935495586277624884192945073504577780123514218564134204833104249608845464968743260633067246684110065738274284507348161726718139189843382748346565424524518127136371821784869190047759906051

noncomputable def p17902 :=
nat_lit
  1917028475608296524754524414050115167504154247844660463312994756811819796526433606321838296869742510593845277692464279985837994123532321587751318897442160640000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p17903 :=
nat_lit
  8720936739200343524319658441159144089715085410185346316063226948799575233026878157795416348692259094940248298205996120987017634317995931054551303153750018877846345017009658656800341224870379520

noncomputable def p17904 :=
@p17899 18446744073709551616 149913806545080235109 p12185
  p17900 p17877 p17901 p17902
  p17903 p17876 p17877 p17878

noncomputable def p17905 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (@Inv.inv.{0} Real Real.instInv
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
          (Enclosure.sfrac false 12 1)))))

noncomputable def p17906 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
        (Enclosure.sfrac false 12 1))
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
        (Enclosure.sfrac false 12 1)))
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
      (Enclosure.sfrac false 12 1)))

noncomputable def p17907 :=
@Enclosure.Real.IsNear.of_eq
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
      (Enclosure.sfrac false 12 1)))
  (p17905
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p17906 (Enclosure.sfrac false 1 16)))))

noncomputable def p17908 :=
BSN.cos_two_pi_p_ne_zero_mk
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
    true 5)
  101779600 100000 12
  (Enclosure.sfrac_ofScientific_eq 101779600 5 100000 (Eq.refl true))

noncomputable def p17909 :=
@Enclosure.Real.IsNear.mulLit_tt
  (@Inv.inv.{0} Real Real.instInv
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
          (Enclosure.sfrac false 12 1)))))

noncomputable def p17910 :=
@p17909
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p17906 (Enclosure.sfrac false 1 16))))
  15188590835

noncomputable def p17911 :=
@p17910 2147483648 6609 8589934592 581339793
  8589934592 4119882557 110729625600000000 8829732251980597155
  18446744073709551616 149913806545080235109 p12185

noncomputable def p17912 :=
@Enclosure.Real.IsNear.of_eq
  (@Inv.inv.{0} Real Real.instInv
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
          (Enclosure.sfrac false 12 1)))))

noncomputable def p17913 :=
@Inv.inv.{0} Real Real.instInv
  (@Neg.neg.{0} Real Real.instNeg
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
          (Enclosure.sfrac false 12 1)))))

noncomputable def p17914 :=
@p17912 (@Neg.neg.{0} Real Real.instNeg p17913) true 15188590835
  2147483648 6609 8589934592
  (BSN.inv_eq_neg_inv_neg
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
          (Enclosure.sfrac false 12 1)))))

noncomputable def p17915 :=
@Enclosure.Real.IsNear.inv_image
  (@Neg.neg.{0} Real Real.instNeg
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
          (Enclosure.sfrac false 12 1)))))

noncomputable def p17916 :=
@Enclosure.Real.IsNear.neg
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
        (Enclosure.sfrac false 12 1))))
  true

noncomputable def p17917 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
        (Enclosure.sfrac false 12 1))))
  true

noncomputable def p17918 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
      (Enclosure.sfrac false 12 1)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 78521033215)
    (@Nat.cast.{0} Real Real.instNatCast 17179869184))
  false

noncomputable def p17919 :=
nat_lit 11050852997876895859587015

noncomputable def p17920 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
      (Enclosure.sfrac false 12 1)))
  false p17919

noncomputable def p17921 :=
nat_lit 1106429199119309281264368863

noncomputable def p17922 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
    (Enclosure.sfrac false 12 1))
  884279719003555 140737488355328 1

noncomputable def p17923 :=
@Enclosure.Real.IsNear.subLit_ff_p p17685 (Enclosure.sfrac false 12 1)
  218655440781 17179869184 41 17179869184 12 1 0

noncomputable def p17924 :=
@p17922 500000000000000 12497010573 17179869184 41
  17179869184 p17919 p2602 p17921
  p5018 d141
  (@p17923 1 12497010573 12497010573 17179869184 41
    17179869184 (p17895 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p17925 :=
@p17918 78521033215 17179869184 259 17179869184 true
  2429026402 17179869184 1 3300000000
  (@p17920 p2602 p17921 p5018
    78521033215 17179869184 259 17179869184
    (p17924 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div 78521033215 17179869184)

noncomputable def p17926 :=
nat_lit 3537866803683029754618839040

noncomputable def p17927 :=
BSN.cos_reduce2
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 78521033215)
    (@Nat.cast.{0} Real Real.instNatCast 17179869184))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast p17926)
    (@Nat.cast.{0} Real Real.instNatCast p2333))
  226375608064910080 72057594037927936 false

noncomputable def p17928 :=
BSN.sin_reduce_arg_pos_rat_q2 78521033215 17179869184 226375608064910080
  72057594037927936 0 p17926 p2333 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p17929 :=
nat_lit
  300225568237978709905949702139034650936757087487852677488996900540209694205346110542301134709086392508168178206533012605709126271207761349131369914629164633767828369140625

noncomputable def p17930 :=
nat_lit
  260819544579600853618192273385535645439867776988962019100203777191300339642451620684853508854296657158793092527473910094710279278459899111199774779379367828369140625

noncomputable def p17931 :=
nat_lit
  1818361271315244163999226614801113084558245021408046184970575365608977982970412917280904404677025387090433706657049239595283763209226645002319842848558049922727828369140625

noncomputable def p17932 :=
BSN.cos_dyadic_bound_f 50276111148875 35184372088832 4 3 17179869184
  6606445313 p17929 p2613 p17930
  p17931 p2616

noncomputable def p17933 :=
@BSN.binarySplit_of_base3 (BSN.cosEvenP 50276111148875) (BSN.cosEvenQ 35184372088832) 0
  3 p17929 p2613 p17930 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p17934 :=
p17932 p17930 2429026402 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p17933 (Eq.refl true))

noncomputable def p17935 :=
@BSN.binarySplit_of_base3 (BSN.cosOddP 50276111148875) (BSN.cosOddQ 35184372088832) 0
  3 p17931 p2616 p17930 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p17936 :=
@BSN.cos_arg_round false 2429026402 17179869184 p17926
  p2333 50276111148875 35184372088832 6606445313 6600000000
  (p17934 (p17935 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p17937 :=
p17927 2429026402 17179869184 0 1000000000000000
  6600000000 3300000000 p17928 BSN.pi_near_15 p17936
  (Eq.refl true) (Eq.refl true)

noncomputable def p17938 :=
@p17916 1214513201 8589934592 3405780739 221459251200000000
  (@p17917 2429026402 17179869184 871879869184
    56693568307200000000 1214513201 8589934592 3405780739
    221459251200000000
    (p17925 (p17937 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p17939 :=
@p17915 1214513201 8589934592 3405780739 221459251200000000
  60754356731 60754369949 8589934592 p17938
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p17940 :=
@Enclosure.Real.IsNear.recentre' p17913 false 121508726680 17179869184
  13218 17179869184 15188590835 2147483648 6609 8589934592
  (p17939 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p17941 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p17906 (Enclosure.sfrac false 1 16))))
  true

noncomputable def p17942 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p17906 (Enclosure.sfrac false 1 16)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Neg.neg.{0} Real Real.instNeg (@Nat.cast.{0} Real Real.instNatCast 14074822185))
    (@Nat.cast.{0} Real Real.instNatCast 8589934592))
  true

noncomputable def p17943 :=
nat_lit 68061663786033362259811813456531045

noncomputable def p17944 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p17906 (Enclosure.sfrac false 1 16)))
  true p17943

noncomputable def p17945 :=
nat_lit 9332483976156250677602661040233359737

noncomputable def p17946 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (p17906 (Enclosure.sfrac false 1 16)) 884279719003555
  140737488355328 1

noncomputable def p17947 :=
@Enclosure.Real.IsNear.subLit_tf
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
        (Enclosure.sfrac false 12 1))
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
        (Enclosure.sfrac false 12 1)))
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
      (Enclosure.sfrac false 12 1)))

noncomputable def p17948 :=
@p17947 (Enclosure.sfrac false 1 16) 58521733573531094103
  295147905179352825856 1729129505211 295147905179352825856 1 16
  0

noncomputable def p17949 :=
@Enclosure.Real.IsNear.subLit_ff_n
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
      (Enclosure.sfrac false 12 1))
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
      (Enclosure.sfrac false 12 1)))
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
    (Enclosure.sfrac false 12 1))
  156175273261673788329

noncomputable def p17950 :=
nat_lit 1005395727214165041645933821952

noncomputable def p17951 :=
@p17949 295147905179352825856 1024754868667 295147905179352825856
  12497010573 17179869184 41 17179869184 p17950
  58521733573531094103 295147905179352825856 1729129505211

noncomputable def p17952 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
    (Enclosure.sfrac false 12 1))
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
    (Enclosure.sfrac false 12 1))
  12497010573 17179869184 41

noncomputable def p17953 :=
@p17952 17179869184 12497010573 17179869184 41
  17179869184 156175273261673788329 295147905179352825856 1024754868667
  295147905179352825856
  (@p17923 1 12497010573 12497010573 17179869184 41
    17179869184 (p17895 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p17954 :=
p17953
  (@p17923 1 12497010573 12497010573 17179869184 41
    17179869184 (p17895 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p17955 :=
@p17951 295147905179352825856 (p17954 (Eq.refl true))
  (@p17923 1 12497010573 12497010573 17179869184 41
    17179869184 (p17895 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p17956 :=
@p17946 500000000000000 76968477647240645719 295147905179352825856
  1729129505211 295147905179352825856 p17943 p2630
  p17945 p10041 d141
  (@p17948 1 1231495642355850331504 76968477647240645719
    295147905179352825856 1729129505211 295147905179352825856
    (p17955 (Eq.refl true) (Eq.refl true))
    (Enclosure.Real.IsNear.const false 1 16) (Eq.refl true)
    (Eq.refl true))

noncomputable def p17957 :=
@p17942 14074822185 8589934592 317 8589934592 true
  581339793 8589934592 1 3300000000
  (@p17944 p2630 p17945 p10041
    14074822185 8589934592 317 8589934592
    (p17956 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_true_div 14074822185 8589934592)

noncomputable def p17958 :=
nat_lit
  5545219755529258505875612251891687799161198104604048512675867154875565056915100591869768299134389130100724593293075716369937397179196851989287367194269455009599840182890625

noncomputable def p17959 :=
nat_lit
  2371846996290861715948415680844930061760197240907247752883885175525342000101426642652159087651261003346383843170663952538086796330448319554301526101904449462890625

noncomputable def p17960 :=
nat_lit
  56400028452405238160443097644967645467867838386489450796051168313971675599341366599769569448444424829737616610378330306522038278625826887329384242722810065238589562806890625

noncomputable def p17961 :=
BSN.cos_dyadic_bound_t 14074822185 8589934592 5 4 8589934592
  3300000000 p17958 p2646 p17959
  p17960 p2649

noncomputable def p17962 :=
@BSN.binarySplit_of_base4 (BSN.cosEvenP 14074822185) (BSN.cosEvenQ 8589934592) 0
  4 p17958 p2646 p17959 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p17963 :=
p17961 p17959 581339793 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p17962 (Eq.refl true))

noncomputable def p17964 :=
@BSN.binarySplit_of_base4 (BSN.cosOddP 14074822185) (BSN.cosOddQ 8589934592) 0 4
  p17960 p2649 p17959 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p17965 :=
p17957
  (BSN.cos_neg_of_bound 14074822185 8589934592 true 581339793 8589934592
    1 3300000000
    (p17963 (p17964 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p17966 :=
p17911
  (p17914
    (@Enclosure.Real.IsNear.neg p17913 false 15188590835 2147483648
      6609 8589934592 (p17940 (Eq.refl true))))
  (@p17941 581339793 8589934592 1054689934592
    28346784153600000000 581339793 8589934592 4119882557
    110729625600000000 (p17965 (Eq.refl true)) (Eq.refl true))

noncomputable def p17967 :=
@p17904 p17879
  (@p17907 false 8829732251980597155 18446744073709551616
    149913806545080235109 p12185
    (BSN.correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
        (Enclosure.sfrac false 12 1))
      (p17908 (Eq.refl true) (Eq.refl true)
        (p17688 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p17966 (Eq.refl true)))

noncomputable def p17968 :=
nat_lit
  582656982719682411082594926254219731310990354256601154784044973399343131202334782505397758140927891125463195003708431618716355771843409100633184605216754710883075

noncomputable def p17969 :=
@Enclosure.Real.IsNear.mulLit_tf
  (Zeta.RiemannSiegel.correctionLinear
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
      (Enclosure.sfrac false 12 1)))
  (@Inv.inv.{0} Real Real.instInv p17685) p17968 p5581

noncomputable def p17970 :=
nat_lit
  819129071088743177375889070844312367508103402474173912459637866414802778374047776877658983092163776054840758861800536024874138978519817879410585587664429453372033881238340064607155732425184613283261990251562544939

noncomputable def p17971 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
      (Enclosure.sfrac false 12 1)))
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 96 1)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi)))

noncomputable def p17972 :=
@Enclosure.Real.IsNear.of_eq
  (Zeta.RiemannSiegel.correctionLinear
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
      (Enclosure.sfrac false 12 1)))
  (@Neg.neg.{0} Real Real.instNeg p17971) true p17968

noncomputable def p17973 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
      (Enclosure.sfrac false 12 1)))
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 96 1)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi)))

noncomputable def p17974 :=
nat_lit
  7845202054711552350208255058479134471874131462753729336840515435867673191517875306141137806505446506949813434088298936969337417160700553884787551356975

noncomputable def p17975 :=
nat_lit
  818347651974035467503297424206899788054160511510766197370822842024033449101168638720817523081476039287721671031890017752304314136471348263332131897344

noncomputable def p17976 :=
nat_lit
  705865948852729560037813276412478781045729116579476278815503860133407962852657890738269117166322077664420299198682195797296315165743245648758402551552079151992087408280617235277428805022441135069222847667

noncomputable def p17977 :=
nat_lit
  15857287887352675921518578933608940821098779383038019717605856070226043190461783104268853624910432641767150281127308474667191658086400000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p17978 :=
@p17973 p17974 p17975 p17976
  p17977 74269213037 70368744177664 1 70368744177664
  p17968 p5581 p17970

noncomputable def p17979 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p17980 :=
p17979
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p17981 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p17980
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p17982 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p17981
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p17906 (Enclosure.sfrac false 1 16)))))

noncomputable def p17983 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (Enclosure.sfrac false 3 1)
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p17984 :=
p17982
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p17983
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 4 1) Real.pi))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p17906 (Enclosure.sfrac false 1 16)))))

noncomputable def p17985 :=
@Neg.neg.{0} Real Real.instNeg
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
          (Enclosure.sfrac false 12 1)))))

noncomputable def p17986 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17984
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 3 1) p17985)
    (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
        (Enclosure.sfrac false 12 1))))

noncomputable def p17987 :=
@Neg.neg.{0} Real Real.instNeg
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 4 1)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
          (Enclosure.sfrac false 12 1)))))

noncomputable def p17988 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17986
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 3 1) p17987)
    (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
        (Enclosure.sfrac false 12 1))))

noncomputable def p17989 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 8 1)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi) Real.pi))
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
        (Enclosure.sfrac false 12 1))))

noncomputable def p17990 :=
@Enclosure.Real.IsNear.of_eq
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
      (Enclosure.sfrac false 12 1)))
  (p17905
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17988
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p17989
        (Zeta.RiemannSiegel.correction
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
            (Enclosure.sfrac false 12 1))))))

noncomputable def p17991 :=
@p17909
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17988
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p17989
      (Zeta.RiemannSiegel.correction
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
          (Enclosure.sfrac false 12 1)))))
  124424927195789

noncomputable def p17992 :=
nat_lit
  63051690939442743919517828362645198695436571607334745861752065792581079690359941257150629212016190004743789074109862390664224135369135275

noncomputable def p17993 :=
nat_lit
  46517678354918840995156723704832290198633047083988355858015372747560914439257467092876227245680868195888801382801035387746214504231337984

noncomputable def p17994 :=
nat_lit
  17018983479213295195406472364020063888830283417514258335654849406405055582936508099015488610178099125001934858494735892656259800288922214820978612990125134387995011082254846068041336907423321

noncomputable def p17995 :=
nat_lit
  2704147372131616735063956684872824920563308418713521584369207642491695058389799971383045026114547108892421126903509811200000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p17996 :=
@p17991 17592186044416 823 4398046511104 p17992
  p17993 p17994 p17995 p17974
  p17975 p17976 p17977

noncomputable def p17997 :=
@p17912 (@Neg.neg.{0} Real Real.instNeg p17913) true 124424927195789
  17592186044416 823 4398046511104
  (BSN.inv_eq_neg_inv_neg
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
          (Enclosure.sfrac false 12 1)))))

noncomputable def p17998 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
      (Enclosure.sfrac false 12 1)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 160811075665031)
    (@Nat.cast.{0} Real Real.instNatCast 35184372088832))
  false

noncomputable def p17999 :=
nat_lit 45264293777630167629558663095

noncomputable def p18000 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
      (Enclosure.sfrac false 12 1)))
  false p17999

noncomputable def p18001 :=
nat_lit 221373758247963340234338963

noncomputable def p18002 :=
@Enclosure.Real.IsNear.subLit_ff_p p17685 (Enclosure.sfrac false 12 1)
  895612685323997 70368744177664 41 70368744177664 12 1
  0

noncomputable def p18003 :=
@p17889
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 101779600 100000)
    (@Inv.inv.{0} Real Real.instInv
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)))
  false 569942018638345041

noncomputable def p18004 :=
@p18003 3518437208883200 254449 17592186044416000
  (BSN.t_div_two_pi_mk
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
      true 5)
    101779600 100000
    (Enclosure.sfrac_ofScientific_eq 101779600 5 100000 (Eq.refl true)))

noncomputable def p18005 :=
@p17892 1 11199533475045 70368744177664 1
  70368744177664 569942018638345041 3518437208883200 254449
  17592186044416000 (Enclosure.Real.IsNear.const false 101779600 100000)
  d198

noncomputable def p18006 :=
@p17888 569942018638345041 3518437208883200 254449
  17592186044416000 447806342661978 447806342662019 35184372088832
  (p18004 (p18005 (Eq.refl true))) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p18007 :=
@Enclosure.Real.IsNear.recentre' p17685 false 895612685323997 70368744177664
  41 70368744177664 895612685323997 70368744177664 41
  70368744177664
  (p18006 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p18008 :=
@p17922 500000000000000 51187755192029 70368744177664 41
  70368744177664 p17999 p12189 p18001
  p14421 d197
  (@p18002 1 51187755192029 51187755192029 70368744177664
    41 70368744177664 (p18007 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p18009 :=
@p17998 160811075665031 35184372088832 129 35184372088832
  true 9949292856225 70368744177664 1 13516800000000
  (@p18000 p12189 p18001 p14421
    160811075665031 35184372088832 129 35184372088832
    (p18008 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div 160811075665031 35184372088832)

noncomputable def p18010 :=
nat_lit 7245551162163843128873201958912

noncomputable def p18011 :=
nat_lit 5070602400912917605986812821504

noncomputable def p18012 :=
BSN.cos_reduce2
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 160811075665031)
    (@Nat.cast.{0} Real Real.instNatCast 35184372088832))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast p18010)
    (@Nat.cast.{0} Real Real.instNatCast p18011))
  226375608064910080 72057594037927936 false

noncomputable def p18013 :=
BSN.sin_reduce_arg_pos_rat_q2 160811075665031 35184372088832 226375608064910080
  72057594037927936 0 p18010 p18011
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p18014 :=
nat_lit
  126150413899704805462683681406048526912108315388587875356877739612535525418521460886105725800836690960570362381741495407499057788792043043318902955998422861082070445828832136916035180202086908270738022839492567015835088051315017102577862151802514181601526745474585902749563907723069751296

noncomputable def p18015 :=
nat_lit
  10460343850733970138662373700096351148992436477462340399977390969724290990382280297311868879270902934843566082629584111727187138425215003831847318481650317773836827394155203433856719284936582135839561820478446054515829545243477152104037762684600513839822287353671714983867580416

noncomputable def p18016 :=
nat_lit
  1284609755234171620486088045225422200803142174069132694543529434770408594219566351476406179770015182901117706258384960259501083775832111343760505593321958462696569927455296024012224534296163844880750897089658555199669319166155560363271462892494619194747603071435952079458899979009855062016

noncomputable def p18017 :=
BSN.cos_dyadic_bound_f 205930949794146816 144115188075855872 5 4
  70368744177664 27060000000001 p18014 p12205
  p18015 p18016 p12208

noncomputable def p18018 :=
@BSN.binarySplit_of_base4 (BSN.cosEvenP 205930949794146816) (BSN.cosEvenQ 144115188075855872)
  0 4 p18014 p12205 p18015
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p18019 :=
p18017 p18015 9949292856225 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p18018 (Eq.refl true))

noncomputable def p18020 :=
@BSN.binarySplit_of_base4 (BSN.cosOddP 205930949794146816) (BSN.cosOddQ 144115188075855872)
  0 4 p18016 p12208 p18015
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p18021 :=
@BSN.cos_arg_round false 9949292856225 70368744177664 p18010
  p18011 205930949794146816 144115188075855872 27060000000001
  27033600000000
  (p18019 (p18020 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p18022 :=
p18012 9949292856225 70368744177664 0 1000000000000000
  27033600000000 13516800000000 p18013 BSN.pi_near_15 p18021
  (Eq.refl true) (Eq.refl true)

noncomputable def p18023 :=
@p17916 9949292856225 70368744177664 1696445057
  453548546457600000000
  (@p17917 9949292856225 70368744177664 1778851572088832
    p12185 9949292856225 70368744177664 1696445057
    453548546457600000000
    (p18009 (p18022 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p18024 :=
@p17915 9949292856225 70368744177664 1696445057
  453548546457600000000 248849854384994 248849854398162 35184372088832
  p18023 (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p18025 :=
@Enclosure.Real.IsNear.recentre' p17913 false 497699708783156 70368744177664
  13168 70368744177664 124424927195789 17592186044416 823
  4398046511104
  (p18024 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p18026 :=
nat_lit
  5530700072344335004790665316470736968373587811735043201154834659799114438263258887279183792712394101327433025724541522833260224836719023275

noncomputable def p18027 :=
@Enclosure.Real.IsNear.subLit_tt_n p17988
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p17989
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
        (Enclosure.sfrac false 12 1))))
  p18026 p17993

noncomputable def p18028 :=
nat_lit
  16966711584646115630685879174340308672921870396966364059495526114277543746538155236658693407377318578348087250139108809559518606638739566356166388851222749623471644371336333428041336907423321

noncomputable def p18029 :=
nat_lit 7135614082525248843555370742246596688105063574951458016728400891765952553463874241625

noncomputable def p18030 :=
nat_lit 60708402882054033466233184588234965832575213720379360039119137804340758912662765568

noncomputable def p18031 :=
nat_lit
  1231607494248528977745221865816736053975614154884925959523258595842491452589566858781565076164536418865068874725712949241

noncomputable def p18032 :=
nat_lit
  3827767455946446063850965677572945377188054522656990204585731829784461153734123234510242524135272897857077235450423528936832064861853582407639314614492943797958833796227114235921379339059030246485375761047054630204211200

noncomputable def p18033 :=
@p18027 p18028 p17995 p18029
  p18030 p18031 p12224 p18032
  p17992 p17993 p17994 p17995

noncomputable def p18034 :=
@Enclosure.Real.IsNear.subLit_tf p17986
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 3 1) p17987)
    (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
        (Enclosure.sfrac false 12 1))))

noncomputable def p18035 :=
nat_lit
  4836591987597124982169944973393728515785895406676368999677380257647692775251064956648134710732223096305165177666153730342770841351279023275

noncomputable def p18036 :=
nat_lit
  16797107583503050341662564683293506359975577761635345901514502985443023076136713579673673415790368473830741084344365376299736853810736219394531609488255440195061347499148402463490066507423321

noncomputable def p18037 :=
nat_lit 1121392091248449281291284281936459744590328239360447672776394936978853648742407184997309514076679521270250859375

noncomputable def p18038 :=
nat_lit
  21256536599540174504742318454117395590089896716331205341622603745407790219553376656351111181967651366793212895521033897595999445465619840743933996845885519

noncomputable def p18039 :=
nat_lit
  338911860562650122602912651409110291544938053996170143699587867261335188748125144491262738432000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p18040 :=
nat_lit
  415650708238431706070235267352957481605251153715546937391541630672439208949162887937522349764080990624852311388655545389970785796611022205086371663470487193432696618822122318400631597009501932217301148368443504620443956472081954971641224064978124800

noncomputable def p18041 :=
@p18034 p18035 p17993 p18036
  p17995 p18037 p12342 p18038
  p18039 p18040 p18026 p17993

noncomputable def p18042 :=
@Enclosure.Real.IsNear.subLit_tf p17984
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 3 1) p17985)
    (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
        (Enclosure.sfrac false 12 1))))

noncomputable def p18043 :=
nat_lit 68336106378829232732286903767760818852370979679074465356814164885845005762705798966117836730180725

noncomputable def p18044 :=
nat_lit
  2173013630811444863174733073642666058989392939960619372497530989570198836398169232277289469922687922689888761246610132459361127

noncomputable def p18045 :=
nat_lit
  1565138511802955550301324290165432712871079728728530376008540271518160190717086924800000000000000000000000000000000000000000000000000000

noncomputable def p18046 :=
nat_lit
  4092477682805155304355674957279965160311278127151293450767732266774125320329554073447940573723414720378371978594680904916209884906626684075

noncomputable def p18047 :=
nat_lit
  5597784395976785647494533452660837379296800845590122917463212977222865363303690156860354625130075149395310001147455961713142460080921691666527919118342496585294740537049467487830022169141107

noncomputable def p18048 :=
nat_lit
  901382457377205578354652228290941640187769472904507194789735880830565019463266657127681675371515702964140375634503270400000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p18049 :=
nat_lit
  20661795567092812181997557598226796347063106400737769307069823672263265235259872600836026615918576365430801800204863746426853893291902621041987175503949664564334099497144624085102983940601522469655741280142817989540339803704108305612800

noncomputable def p18050 :=
@p18042 p18043 p12238 p18044
  p18045 p18046 p17993 p18047
  p18048 p18049 p18035 p17993

noncomputable def p18051 :=
@Enclosure.Real.IsNear.subLit_tt_n
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p17981
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p17906 (Enclosure.sfrac false 1 16)))))

noncomputable def p18052 :=
@p18051
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p17983
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 4 1) Real.pi))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p17906 (Enclosure.sfrac false 1 16)))))

noncomputable def p18053 :=
nat_lit 99484941975286739146246500604171526071898652688665220546544241384181367092649772398416528512427125

noncomputable def p18054 :=
nat_lit
  612022788862719599720862192581879468095577119151357288226956528310308235059671512641730517487081908256748615070610132459361127

noncomputable def p18055 :=
nat_lit 44696387058505831547164530425130951915170435800015625925

noncomputable def p18056 :=
nat_lit 12232906109307018708535492585966161676394327249029078287232689310363146781

noncomputable def p18057 :=
nat_lit 12265409859191842727844645049956598828289228800000000000000000000000000000000000000

noncomputable def p18058 :=
nat_lit
  418899113222771290883482777199838052646479957023351097851404167371040842021318621954429372242824428065449637336474367001860054408267331135589423933030400

noncomputable def p18059 :=
@p18052 p18053 p12238 p18054
  p18045 p18055 p2977 p18056
  p18057 p18058 p18043 p12238

noncomputable def p18060 :=
nat_lit 2834029713832584062260189750405581960035087259255192658767536871909286495133836470375

noncomputable def p18061 :=
@Enclosure.Real.IsNear.mulLit_ft p17981
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p17906 (Enclosure.sfrac false 1 16))))
  p18060

noncomputable def p18062 :=
nat_lit 619158528608379977355160873042695623096045309158399980130654378151148153378308481392749761918764800310261

noncomputable def p18063 :=
@p18061 p12222 p18062 p14484
  35103704625859 35184372088832 4119882557 453548546457600000000
  p18053 p12238 p18054 p18045

noncomputable def p18064 :=
@Enclosure.Real.IsNear.mulLit_ff p17980
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p18065 :=
nat_lit 200264021467338633306795509726175212776929446113384662225

noncomputable def p18066 :=
nat_lit 955782487782419873062116383737748053385923814365239777298901235691

noncomputable def p18067 :=
nat_lit 14151467113601283188574865335

noncomputable def p18068 :=
nat_lit 1106566559784913043878018271

noncomputable def p18069 :=
@p18064 p18065 p12261 p18066
  p14489 p18067 p12265 p18068
  p14492 p18060 p12222 p18062

noncomputable def p18070 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p18071 :=
@p18070
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p18072 :=
@p18071 p18067 p12265 p18068
  p14492 p18067 p12265 p18068
  p14492 p18065 p12261 p18066

noncomputable def p18073 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
        (Enclosure.sfrac false 12 1)))
    (Enclosure.sfrac false 1 1))
  884279719003555

noncomputable def p18074 :=
@p18073 140737488355328 1 500000000000000 16003383103197
  35184372088832 41 35184372088832 p18067 p12265
  p18068 p14492

noncomputable def p18075 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 2 1)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
      (Enclosure.sfrac false 12 1)))
  (Enclosure.sfrac false 1 1) 51187755192029 35184372088832

noncomputable def p18076 :=
@p18075 41 35184372088832 1 1 0 1
  16003383103197 16003383103197 35184372088832 41 35184372088832

noncomputable def p18077 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 2 1)
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
    (Enclosure.sfrac false 12 1))
  2 1 0 1

noncomputable def p18078 :=
@p18077 51187755192029 70368744177664 41 70368744177664
  51187755192029 35184372088832 41 35184372088832
  (Enclosure.Real.IsNear.const false 2 1)
  (@p18002 1 51187755192029 51187755192029 70368744177664
    41 70368744177664 (p18007 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p18079 :=
@p18072 p14489
  (p18074 d197
    (p18076 (p18078 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (p18074 d197
    (p18076 (p18078 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))

noncomputable def p18080 :=
@p18069 p14484 (p18079 (Eq.refl true))
  (p18074 d197
    (p18076 (p18078 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p18081 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p17906 (Enclosure.sfrac false 1 16))))
  true

noncomputable def p18082 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p17906 (Enclosure.sfrac false 1 16)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Neg.neg.{0} Real Real.instNeg (@Nat.cast.{0} Real Real.instNatCast 14412617959003))
    (@Nat.cast.{0} Real Real.instNatCast 8796093022208))
  true

noncomputable def p18083 :=
nat_lit 1141885237911902588038963395936810620294405

noncomputable def p18084 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p17906 (Enclosure.sfrac false 1 16)))
  true p18083

noncomputable def p18085 :=
nat_lit 191140361010059980041577712346567706082493

noncomputable def p18086 :=
nat_lit 1291316778359034102072284471

noncomputable def p18087 :=
nat_lit 981831768537689033347503415

noncomputable def p18088 :=
@p17947 (Enclosure.sfrac false 1 16) p18087
  p12265 7082514437032283 p12265 1 16 0

noncomputable def p18089 :=
nat_lit 20661068453744545633156551536

noncomputable def p18090 :=
nat_lit 2620186281599091846665136841

noncomputable def p18091 :=
@Enclosure.Real.IsNear.subLit_ff_n
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
      (Enclosure.sfrac false 12 1))
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
      (Enclosure.sfrac false 12 1)))
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
    (Enclosure.sfrac false 12 1))
  p18090

noncomputable def p18092 :=
nat_lit 69090268545732053264717915269911606722560

noncomputable def p18093 :=
@p18091 p12265 4197395925748059 p12265
  51187755192029 70368744177664 41 70368744177664 p18092
  p18087 p12265 7082514437032283

noncomputable def p18094 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
    (Enclosure.sfrac false 12 1))
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
    (Enclosure.sfrac false 12 1))
  51187755192029 70368744177664 41

noncomputable def p18095 :=
@p18094 70368744177664 51187755192029 70368744177664 41
  70368744177664 p18090 p12265 4197395925748059
  p12265
  (@p18002 1 51187755192029 51187755192029 70368744177664
    41 70368744177664 (p18007 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p18096 :=
p18095
  (@p18002 1 51187755192029 51187755192029 70368744177664
    41 70368744177664 (p18007 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p18097 :=
@p18093 p12265 (p18096 (Eq.refl true))
  (@p18002 1 51187755192029 51187755192029 70368744177664
    41 70368744177664 (p18007 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p18098 :=
@p17946 500000000000000 p18086 p12265
  7082514437032283 p12265 p18083 p12284
  p18085 p12286 d197
  (@p18088 1 p18089 p18086 p12265
    7082514437032283 p12265
    (p18097 (Eq.refl true) (Eq.refl true))
    (Enclosure.Real.IsNear.const false 1 16) (Eq.refl true)
    (Eq.refl true))

noncomputable def p18099 :=
@p18082 14412617959003 8796093022208 317 35184372088832
  true 35103704625859 35184372088832 1 13516800000000
  (@p18084 p12284 p18085 p12286
    14412617959003 8796093022208 317 35184372088832
    (p18098 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_true_div 14412617959003 8796093022208)

noncomputable def p18100 :=
nat_lit
  27502420011772306571261582472206991831614423883277889885667445554600349644345662154333659027276873023469819484516071434839752858604109842251786970304710157545048728201517699851754702753620402103452241416428135420290671041

noncomputable def p18101 :=
nat_lit
  456778371644818173076789776443063775907022685762947868640820701988737698700543484457581868374305692808124391530773558881386970915902830864099131260227990136930080074302757761035062747682883102926047962842212100919525376000

noncomputable def p18102 :=
nat_lit
  3466458428522225676430010323209122152480810099127092126066789861705517409048356349349626816864992364852099142611187372187802013494550517838938233576304828702467868094186169294999721367989247305535680270256054721

noncomputable def p18103 :=
nat_lit
  223618898109399127825249286015839236213055070371810974132398879790713214448669219536058492366661096019643223803415729072514786434511315145113795407092041609943740034822692617219023908189196932601331116999985251540175692225

noncomputable def p18104 :=
nat_lit
  26036367183754635865377017257254635226700293088488028512526780013358048825930978614082166497335424490063090317254092856239057342206461359253650481832995437805014564235257192378998576617924336866784733882006089752412946432000

noncomputable def p18105 :=
BSN.sin_dyadic_bound_f 14412617959003 8796093022208 5 4 35184372088832
  13516800000000 p18100 p18101 p18102
  p18103 p18104

noncomputable def p18106 :=
@BSN.binarySplit_of_base4 (BSN.sinEvenP 14412617959003) (BSN.sinEvenQ 8796093022208) 0
  4 p18100 p18101 p18102 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p18107 :=
p18105 p18102 35103704625859 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p18106 (Eq.refl true))

noncomputable def p18108 :=
@BSN.binarySplit_of_base4 (BSN.sinOddP 14412617959003) (BSN.sinOddQ 8796093022208) 0
  4 p18103 p18104 p18102 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p18109 :=
p18099
  (BSN.sin_neg_of_bound 14412617959003 8796093022208 false 35103704625859
    35184372088832 1 13516800000000
    (p18107 (p18108 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p18110 :=
p18063 p18080
  (@p18081 35103704625859 35184372088832 4320009972088832
    p12185 35103704625859 35184372088832 4119882557
    453548546457600000000 (p18109 (Eq.refl true))
    (Eq.refl true))

noncomputable def p18111 :=
nat_lit 37541566088110176724863775471896073533797775

noncomputable def p18112 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p17983
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 4 1) Real.pi))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p17906 (Enclosure.sfrac false 1 16))))
  p18111

noncomputable def p18113 :=
nat_lit 89596795049031412035541791171733187281588336254588171

noncomputable def p18114 :=
@p18112 p12314 p18113 p14536
  1190583977067 17592186044416 4119882557 453548546457600000000
  p18055 p2977 p18056 p18057

noncomputable def p18115 :=
nat_lit 42454401340803849565724596005

noncomputable def p18116 :=
nat_lit 3319699679354739131634054813

noncomputable def p18117 :=
@Enclosure.Real.IsNear.mulLit_ff p17983
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 4 1) Real.pi)
  p18115 p12265 p18116 p14492

noncomputable def p18118 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 3 1)
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p18119 :=
@p18118 3 1 0 1 p18067
  p12265 p18068 p14492 p18115
  p12265 p18116

noncomputable def p18120 :=
@p18119 p14492 (Enclosure.Real.IsNear.const false 3 1)
  (p18074 d197
    (p18076 (p18078 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p18121 :=
@p18117 884279719003555 70368744177664 1 250000000000000
  p18111 p12314 p18113 p14536
  p18120 d199 (Eq.refl true)

noncomputable def p18122 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p17906 (Enclosure.sfrac false 1 16)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Neg.neg.{0} Real Real.instNeg (@Nat.cast.{0} Real Real.instNatCast 14412617959003))
    (@Nat.cast.{0} Real Real.instNatCast 8796093022208))
  true

noncomputable def p18123 :=
@p18122 14412617959003 8796093022208 317 35184372088832
  true 2381167954134 35184372088832 1 13516800000000
  (@p18084 p12284 p18085 p12286
    14412617959003 8796093022208 317 35184372088832
    (p18098 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_true_div 14412617959003 8796093022208)

noncomputable def p18124 :=
nat_lit
  8104347845950574350396142081856992338321932807809456419171168033572813518137648507857450694811664537476596464150975276601266034247236067305415813905522962130606736784771689357524708522262169532533320435219850510556209601

noncomputable def p18125 :=
nat_lit
  26869315979106951357458222143709633876883687397820462861224747175808099923561381438681286374959158400477905384163150522434527700935460639064654780013411184525298827900162221237356632216640182525061644873071300054089728000

noncomputable def p18126 :=
nat_lit
  82428734880887942994595843961398600589398693547839812331975326646230686641878374691395530626878783993362656078464410327955451610517196566746530971983471354346394850145842378076941469986886453146051225233499269055386755521

noncomputable def p18127 :=
nat_lit
  4111005344803363557691107987987573983163204171866530817767386317898639288304891360118236815368751235273119523776962029932482738243125477776892181342051911232370720668724819849315564729145947926334431665579908908275728384000

noncomputable def p18128 :=
BSN.cos_dyadic_bound_t 14412617959003 8796093022208 5 4 35184372088832
  13516800000000 p18124 p18125 p18102
  p18126 p18127

noncomputable def p18129 :=
@BSN.binarySplit_of_base4 (BSN.cosEvenP 14412617959003) (BSN.cosEvenQ 8796093022208) 0
  4 p18124 p18125 p18102 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p18130 :=
p18128 p18102 2381167954134 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p18129 (Eq.refl true))

noncomputable def p18131 :=
@BSN.binarySplit_of_base4 (BSN.cosOddP 14412617959003) (BSN.cosOddQ 8796093022208) 0
  4 p18126 p18127 p18102 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p18132 :=
p18123
  (BSN.cos_neg_of_bound 14412617959003 8796093022208 true 2381167954134
    35184372088832 1 13516800000000
    (p18130 (p18131 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p18133 :=
p18114 p18121
  (@p17941 2381167954134 35184372088832 4320009972088832
    p12185 1190583977067 17592186044416 4119882557
    453548546457600000000 (p18132 (Eq.refl true))
    (Eq.refl true))

noncomputable def p18134 :=
nat_lit 184801652648011342361277389565

noncomputable def p18135 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 3 1) p17985)
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
      (Enclosure.sfrac false 12 1)))
  p18134

noncomputable def p18136 :=
nat_lit 45784251050144158996114769966946119

noncomputable def p18137 :=
nat_lit 22145243963808213340270027832351721241173339089883931489775434766031457832934753789845381638536885266191213255

noncomputable def p18138 :=
nat_lit 4697085165547666455778961193578674054751365097816639741414581943064418050229216886927397996769537406063869952

noncomputable def p18139 :=
nat_lit
  230985268621369440166710717536061682930949151184786035314624871487674320700920585764935425346459851942388854944494940659474648047655695897266439

noncomputable def p18140 :=
nat_lit
  694091490432307451090765110085857877084033134584156454296755952151214466556160295918106088308736000000000000000000000000000000000000000000000000000000

noncomputable def p18141 :=
@p18135 p12189 p18136 p12340
  p18137 p18138 p18139 p18140
  p18046 p17993 p18047 p18048

noncomputable def p18142 :=
nat_lit 61600550882670447453759129855

noncomputable def p18143 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 3 1) p17985
  3 1 0 1 p18142 p12189

noncomputable def p18144 :=
@Enclosure.Real.IsNear.neg
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
          (Enclosure.sfrac false 12 1)))))

noncomputable def p18145 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
        (Enclosure.sfrac false 12 1))))
  884279719003555

noncomputable def p18146 :=
@p18145 140737488355328 1 500000000000000 69661838396661
  70368744177664 1696445057 453548546457600000000 p18142
  p12189 p18136 p12348

noncomputable def p18147 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
        (Enclosure.sfrac false 12 1))))
  true

noncomputable def p18148 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
      (Enclosure.sfrac false 12 1)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 160811075665031)
    (@Nat.cast.{0} Real Real.instNatCast 35184372088832))
  false

noncomputable def p18149 :=
@p18148 160811075665031 35184372088832 129 35184372088832
  true 69661838396661 70368744177664 1 13516800000000
  (@p18000 p12189 p18001 p14421
    160811075665031 35184372088832 129 35184372088832
    (p18008 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div 160811075665031 35184372088832)

noncomputable def p18150 :=
BSN.sin_reduce2
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 160811075665031)
    (@Nat.cast.{0} Real Real.instNatCast 35184372088832))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast p18010)
    (@Nat.cast.{0} Real Real.instNatCast p18011))
  226375608064910080 72057594037927936 false

noncomputable def p18151 :=
nat_lit
  428439281740869047279433331570494164802525818328557124085354517374264643575833422586969184325954084408222139790294867552802653633454853558375406493088222747588752436314556396910552908975185376192128816996617639672609850859914943958145733278503035238466436510728394776658707077991535476736

noncomputable def p18152 :=
nat_lit
  3485749663051140857526936838028053268310867326909783459259591305830848848456245319216882293429565997601685175643700234618899153077265876429589415222207928271006558328360411059499016390695645849662950367051910703653718860633874575456812707617585299813730870721511336335311979545566191288320

noncomputable def p18153 :=
BSN.sin_dyadic_bound_f 205930949794146816 144115188075855872 5 4
  70368744177664 27060000000001 p18151 p12357
  p18015 p18152 p12359

noncomputable def p18154 :=
@BSN.binarySplit_of_base4 (BSN.sinEvenP 205930949794146816) (BSN.sinEvenQ 144115188075855872)
  0 4 p18151 p12357 p18015
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p18155 :=
p18153 p18015 69661838396661 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p18154 (Eq.refl true))

noncomputable def p18156 :=
@BSN.binarySplit_of_base4 (BSN.sinOddP 205930949794146816) (BSN.sinOddQ 144115188075855872)
  0 4 p18152 p12359 p18015
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p18157 :=
@BSN.sin_arg_round false 69661838396661 70368744177664 p18010
  p18011 205930949794146816 144115188075855872 27060000000001
  27033600000000
  (p18155 (p18156 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p18158 :=
p18150 69661838396661 70368744177664 0 1000000000000000
  27033600000000 13516800000000 p18013 BSN.pi_near_15 p18157
  (Eq.refl true) (Eq.refl true)

noncomputable def p18159 :=
p18146 d197
  (@p18147 69661838396661 70368744177664 1778851572088832
    p12185 69661838396661 70368744177664 1696445057
    453548546457600000000
    (p18149 (p18158 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p18160 :=
@Neg.neg.{0} Real Real.instNeg
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p17980
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p17906 (Enclosure.sfrac false 1 16)))))

noncomputable def p18161 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18160
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 4 1) Real.pi)
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p17906 (Enclosure.sfrac false 1 16)))))

noncomputable def p18162 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18161
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) p17985)
    (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
        (Enclosure.sfrac false 12 1))))

noncomputable def p18163 :=
@Enclosure.Real.IsNear.of_eq
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
      (Enclosure.sfrac false 12 1)))
  (p17905
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18162
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p17987
        (Zeta.RiemannSiegel.correction
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
            (Enclosure.sfrac false 12 1))))))

noncomputable def p18164 :=
@p17909
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18162
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p17987
      (Zeta.RiemannSiegel.correction
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
          (Enclosure.sfrac false 12 1)))))
  124424927195789

noncomputable def p18165 :=
nat_lit 177980766900201090490867288403032824058092037300324472754420073478655173867390221201599882149795

noncomputable def p18166 :=
nat_lit 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072

noncomputable def p18167 :=
nat_lit
  1855726927880119882071276755275806657339582381544571555884895369563667892719938272092759568459068429306077922594177687460368956919

noncomputable def p18168 :=
nat_lit
  39454533318366171163845883147920282970291801495031703228548619344520288140993232896000000000000000000000000000000000000000000000000000000

noncomputable def p18169 :=
@p18164 17592186044416 823 4398046511104 p18165
  p18166 p18167 p18168 p18137
  p18138 p18139 p18140

noncomputable def p18170 :=
nat_lit 535378958543230146956925354130218867521260770460225720483849287691341535311232020063440870490205

noncomputable def p18171 :=
@Enclosure.Real.IsNear.subLit_ff_n p18162
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p17987
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
        (Enclosure.sfrac false 12 1))))
  p18170 p18166

noncomputable def p18172 :=
nat_lit
  1836000426195923038411582658977328561032482401972169331409555116456282506832216698318605132959228536371332894341738694154768956919

noncomputable def p18173 :=
nat_lit 1152494794263588071642323627438466880375763807072454699631343776954375

noncomputable def p18174 :=
nat_lit 7416990793937398739387450158166459523682267144900827429906550437602273796064768693556529026523

noncomputable def p18175 :=
nat_lit
  76773631734527860758232753815560806046446312484107219063208958341550066277903544560044666914637962803299175968907641185857434504650400216171702840941623836692971520

noncomputable def p18176 :=
@p18171 p18172 p18168 p18173
  p12388 p18174 p12383 p18175
  p18165 p18166 p18167 p18168

noncomputable def p18177 :=
@Enclosure.Real.IsNear.subLit_ff_p p18161
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) p17985)
    (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
        (Enclosure.sfrac false 12 1))))

noncomputable def p18178 :=
nat_lit 5646622148191779585682859528641547416363790055117735052404271556986715

noncomputable def p18179 :=
nat_lit 330007102180669067256980074373472651221432978619570781259036653508780094763967110329377

noncomputable def p18180 :=
nat_lit 2959710863437884843384122839090764421567298095678268611951292183080613876146643149446990080851875

noncomputable def p18181 :=
nat_lit
  1828457700120239898138705606292315319128516546344383948536959371941134109505098310615242397151098004327993004964458694154768956919

noncomputable def p18182 :=
nat_lit
  230940610704642210435988359451266587247531757674928912672254987986964170018376699413423649122659244079975380347087171519995244461262853501871552380329201922190868480

noncomputable def p18183 :=
@p18177 p18178 p12388 p18179
  p16696 p18180 p18166 p18181
  p18168 p18182 p18170 p18166

noncomputable def p18184 :=
@Enclosure.Real.IsNear.subLit_ft p18160
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 4 1) Real.pi)
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p17906 (Enclosure.sfrac false 1 16)))))

noncomputable def p18185 :=
nat_lit 238431135142015095086460947527087164978431613058134976972238941194075

noncomputable def p18186 :=
nat_lit 398869229216507496521985689714651749221960718847891399934383535942738108291901330988131

noncomputable def p18187 :=
nat_lit 31041494062538390323565928745

noncomputable def p18188 :=
nat_lit 111183348379677597270614143031008619

noncomputable def p18189 :=
nat_lit 13980359287924459961364192772883933156354235464553977329740565883087821645831500678041723805368320

noncomputable def p18190 :=
@p18184 p18185 p12388 p18186
  p16688 p18187 p2333 p18188
  p12402 p18189 p18178 p12388

noncomputable def p18191 :=
@Enclosure.Real.IsNear.neg
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p17980
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p17906 (Enclosure.sfrac false 1 16)))))

noncomputable def p18192 :=
@Enclosure.Real.IsNear.mulLit_ft p17980
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p17906 (Enclosure.sfrac false 1 16))))
  p18065

noncomputable def p18193 :=
@p18192 p12261 p18066 p14489
  1190583977067 17592186044416 4119882557 453548546457600000000
  p18185 p12388 p18186 p16688

noncomputable def p18194 :=
p18193 (p18079 (Eq.refl true))
  (@p17941 2381167954134 35184372088832 4320009972088832
    p12185 1190583977067 17592186044416 4119882557
    453548546457600000000 (p18132 (Eq.refl true))
    (Eq.refl true))

noncomputable def p18195 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 4 1) Real.pi)
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p17906 (Enclosure.sfrac false 1 16))))
  884279719003555

noncomputable def p18196 :=
@p18195 70368744177664 1 250000000000000 35103704625859
  35184372088832 4119882557 453548546457600000000 p18187
  p2333 p18188 p12402

noncomputable def p18197 :=
p18196 d199
  (@p18081 35103704625859 35184372088832 4320009972088832
    p12185 35103704625859 35184372088832 4119882557
    453548546457600000000 (p18109 (Eq.refl true))
    (Eq.refl true))

noncomputable def p18198 :=
@p18183 p18172 p18168
  (@p18190 p18179 p16696
    (@p18191 true p18185 p12388 p18186
      p16688 (p18194 (Eq.refl true)))
    (p18197 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p18199 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 2 1) p17985)
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
      (Enclosure.sfrac false 12 1)))
  p18142

noncomputable def p18200 :=
nat_lit 48046824598617588255138230254460815585627971921008577819565431244125

noncomputable def p18201 :=
nat_lit 53919893334301279589334030174039261347274288845081144962207220498432

noncomputable def p18202 :=
nat_lit 226154288686145268192728869634959983122024675949165954572356933890669724524997764489

noncomputable def p18203 :=
nat_lit 60762344798543069793930441616650210907870800702411854084833280000000000000000000000000000000

noncomputable def p18204 :=
@p18199 p12265 p18136 p12402
  p18200 p18201 p18202 p18203
  p18180 p18166 p18181 p18168

noncomputable def p18205 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 2 1) p17985
  2 1 0 1 p18142 p12189

noncomputable def p18206 :=
@Neg.neg.{0} Real Real.instNeg
  (p17979
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p17906 (Enclosure.sfrac false 1 16)))))

noncomputable def p18207 :=
@Enclosure.Real.IsNear.of_eq
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
      (Enclosure.sfrac false 12 1)))
  (p17905
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18206
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p17985
        (Zeta.RiemannSiegel.correction
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
            (Enclosure.sfrac false 12 1))))))

noncomputable def p18208 :=
@p17909
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18206
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p17985
      (Zeta.RiemannSiegel.correction
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
          (Enclosure.sfrac false 12 1)))))
  124424927195789

noncomputable def p18209 :=
nat_lit 386151116833795267096007930187497871243661257748484625

noncomputable def p18210 :=
nat_lit 5418249398689925625816043098778088288251529705252175444996975778242907

noncomputable def p18211 :=
nat_lit 10361818249045268736483156138203334690138740490240000000000000000000000000000000

noncomputable def p18212 :=
@p18208 17592186044416 823 4398046511104 p18209
  p14476 p18210 p18211 p18200
  p18201 p18202 p18203

noncomputable def p18213 :=
nat_lit 496768921578416875323293749677977483697765

noncomputable def p18214 :=
@Enclosure.Real.IsNear.subLit_ff_n p18206
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p17985
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
        (Enclosure.sfrac false 12 1))))
  p18213 p12427

noncomputable def p18215 :=
nat_lit 2279978500418542977333489696569273966630893636447

noncomputable def p18216 :=
nat_lit 68538318532659724696602551545705267200000000000000000000000

noncomputable def p18217 :=
nat_lit 9125402406325206944149165641519333053963758837958414865

noncomputable def p18218 :=
nat_lit 1691185251250040906316498757880164953751488335681671105654531126080969

noncomputable def p18219 :=
nat_lit 67277013004988261605689850648184503903016646992965576585561919629129798958131201551649210368000

noncomputable def p18220 :=
@p18214 p18215 p18216 p18217
  p14476 p18218 p12424 p18219
  p18209 p14476 p18210 p18211

noncomputable def p18221 :=
@Enclosure.Real.IsNear.neg
  (p17979
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p17906 (Enclosure.sfrac false 1 16)))))

noncomputable def p18222 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p18223 :=
@p18222
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p17906 (Enclosure.sfrac false 1 16))))
  p18067

noncomputable def p18224 :=
@p18223 p12265 p18068 p14492
  35103704625859 35184372088832 4119882557 453548546457600000000
  p18213 p12427 p18215 p18216

noncomputable def p18225 :=
p18224
  (p18074 d197
    (p18076 (p18078 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (@p18081 35103704625859 35184372088832 4320009972088832
    p12185 35103704625859 35184372088832 4119882557
    453548546457600000000 (p18109 (Eq.refl true))
    (Eq.refl true))

noncomputable def p18226 :=
@Enclosure.Real.IsNear.mulLit_ff p17985
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
      (Enclosure.sfrac false 12 1)))
  p18142 p12189 p18136

noncomputable def p18227 :=
nat_lit 148138324667034395394970863

noncomputable def p18228 :=
@p17909
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p17906 (Enclosure.sfrac false 1 16))))
  124424927195789

noncomputable def p18229 :=
@p18228 17592186044416 823 4398046511104 1190583977067
  17592186044416 4119882557 453548546457600000000 p18227
  p976 204554393900707322985039 p16737

noncomputable def p18230 :=
p18229
  (p17997
    (@Enclosure.Real.IsNear.neg p17913 false 124424927195789 17592186044416
      823 4398046511104 (p18025 (Eq.refl true))))
  (@p17941 2381167954134 35184372088832 4320009972088832
    p12185 1190583977067 17592186044416 4119882557
    453548546457600000000 (p18132 (Eq.refl true))
    (Eq.refl true))

noncomputable def p18231 :=
@p18226 p12348 p18227 p976
  204554393900707322985039 p16737 p18217 p14476
  p18218 p12424
  (@p18144 true p18142 p12189 p18136
    p12348 (p18159 (Eq.refl true)))
  (@p17907 false p18227 p976
    204554393900707322985039 p16737
    (BSN.correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
        (Enclosure.sfrac false 12 1))
      (p17908 (Eq.refl true) (Eq.refl true)
        (p17688 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p18230 (Eq.refl true)))

noncomputable def p18232 :=
p18212
  (p17997
    (@Enclosure.Real.IsNear.neg p17913 false 124424927195789 17592186044416
      823 4398046511104 (p18025 (Eq.refl true))))
  (p18220
    (@p18221 true p18213 p12427 p18215
      p18216 (p18225 (Eq.refl true)))
    (p18231 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p18233 :=
p18204
  (@p18205 p18136 p12348 p18142
    p12265 p18136 p12402
    (Enclosure.Real.IsNear.const false 2 1)
    (@p18144 true p18142 p12189 p18136
      p12348 (p18159 (Eq.refl true)))
    (Eq.refl true))
  (@p18207 false p18200 p18201 p18202
    p18203
    (BSN.deriv_correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
        (Enclosure.sfrac false 12 1))
      (p17908 (Eq.refl true) (Eq.refl true)
        (p17688 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p18232 (Eq.refl true)))

noncomputable def p18234 :=
nat_lit 7779855731823702199474066222986359542955625

noncomputable def p18235 :=
nat_lit 1235462901154328841315383345265074381416582974776210529889073

noncomputable def p18236 :=
@Enclosure.Real.IsNear.mulLit_ff p17987
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
      (Enclosure.sfrac false 12 1)))
  p18234 p12450 p18235

noncomputable def p18237 :=
@Enclosure.Real.IsNear.neg
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 4 1)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
          (Enclosure.sfrac false 12 1)))))

noncomputable def p18238 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 4 1)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
        (Enclosure.sfrac false 12 1))))
  p1068

noncomputable def p18239 :=
@p18238 p1070 p1071 p1072
  9949292856225 70368744177664 1696445057 453548546457600000000
  p18234 p12450 p18235 p12453

noncomputable def p18240 :=
p18239 d201
  (@p17917 9949292856225 70368744177664 1778851572088832
    p12185 9949292856225 70368744177664 1696445057
    453548546457600000000
    (p18009 (p18022 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p18241 :=
@p18236 p12453 p18227 p976
  204554393900707322985039 p16737 p18173 p12388
  p18174 p12383
  (@p18237 true p18234 p12450 p18235
    p12453 (p18240 (Eq.refl true)))
  (@p17907 false p18227 p976
    204554393900707322985039 p16737
    (BSN.correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
        (Enclosure.sfrac false 12 1))
      (p17908 (Eq.refl true) (Eq.refl true)
        (p17688 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p18230 (Eq.refl true)))

noncomputable def p18242 :=
p18169
  (p17997
    (@Enclosure.Real.IsNear.neg p17913 false 124424927195789 17592186044416
      823 4398046511104 (p18025 (Eq.refl true))))
  (p18176
    (p18198 (p18233 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true))
    (p18241 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p18243 :=
p18141
  (@p18143 p18136 p12348 p18134
    p12189 p18136 p12340
    (Enclosure.Real.IsNear.const false 3 1)
    (@p18144 true p18142 p12189 p18136
      p12348 (p18159 (Eq.refl true)))
    (Eq.refl true))
  (@p18163 false p18137 p18138 p18139
    p18140
    (BSN.iteratedDeriv_two_correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
        (Enclosure.sfrac false 12 1))
      (p17908 (Eq.refl true) (Eq.refl true)
        (p17688 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p18242 (Eq.refl true)))

noncomputable def p18244 :=
@p18050 p18036 p17995
  (@p18059 p18044 p18045
    (p18110 (Eq.refl true)) (p18133 (Eq.refl true))
    (Eq.refl true) (Eq.refl true))
  (p18243 (Eq.refl true)) (Eq.refl true) (Eq.refl true)

noncomputable def p18245 :=
nat_lit 23339567195471106598422198668959078628866875

noncomputable def p18246 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 3 1) p17987)
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
      (Enclosure.sfrac false 12 1)))
  p18245

noncomputable def p18247 :=
@p18246 p12450 p18235 p12464
  p18200 p18201 p18202 p18203
  p18037 p12342 p18038 p18039

noncomputable def p18248 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 3 1) p17987
  3 1 0 1 p18234 p12450

noncomputable def p18249 :=
p18247
  (@p18248 p18235 p12453 p18245
    p12450 p18235 p12464
    (Enclosure.Real.IsNear.const false 3 1)
    (@p18237 true p18234 p12450 p18235
      p12453 (p18240 (Eq.refl true)))
    (Eq.refl true))
  (@p18207 false p18200 p18201 p18202
    p18203
    (BSN.deriv_correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
        (Enclosure.sfrac false 12 1))
      (p17908 (Eq.refl true) (Eq.refl true)
        (p17688 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p18232 (Eq.refl true)))

noncomputable def p18250 :=
nat_lit 48168589043812478759291864915827165695677014854624035736375

noncomputable def p18251 :=
nat_lit 33347918873730756919707605218928072619114317536187330852980197648761115385908181997591

noncomputable def p18252 :=
@Enclosure.Real.IsNear.mulLit_tf p17989
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
      (Enclosure.sfrac false 12 1)))
  p18250 p14074 p18251

noncomputable def p18253 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 8 1)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi) Real.pi))
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
        (Enclosure.sfrac false 12 1))))

noncomputable def p18254 :=
@p18253 p1059 p1061 p1062
  p1063 69661838396661 70368744177664 1696445057
  453548546457600000000 p18250 p14074 p18251

noncomputable def p18255 :=
@p18254 p12472 d202
  (@p18147 69661838396661 70368744177664 1778851572088832
    p12185 69661838396661 70368744177664 1696445057
    453548546457600000000
    (p18149 (p18158 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p18256 :=
@p18252 p12472 p18227 p976
  204554393900707322985039 p16737 p18029 p18030
  p18031 p12224 (p18255 (Eq.refl true))
  (@p17907 false p18227 p976
    204554393900707322985039 p16737
    (BSN.correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
        (Enclosure.sfrac false 12 1))
      (p17908 (Eq.refl true) (Eq.refl true)
        (p17688 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p18230 (Eq.refl true)))

noncomputable def p18257 :=
p17996
  (p17997
    (@Enclosure.Real.IsNear.neg p17913 false 124424927195789 17592186044416
      823 4398046511104 (p18025 (Eq.refl true))))
  (p18033
    (@p18041 p18028 p17995 p18244
      (p18249 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true))
    (p18256 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p18258 :=
@p17978 p2559
  (@p17990 false p17974 p17975 p17976
    p17977
    (BSN.iteratedDeriv_three_correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
        (Enclosure.sfrac false 12 1))
      (p17908 (Eq.refl true) (Eq.refl true)
        (p17688 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p18257 (Eq.refl true)))

noncomputable def p18259 :=
@p17969 p17970 p2559 1349831059 17179869184
  1 17179869184 p17900 p17877 p17901
  p17902
  (@p17972 p5581 p17970 p2559
    (BSN.correctionLinear_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p17685
        (Enclosure.sfrac false 12 1)))
    (@Enclosure.Real.IsNear.neg p17971 false p17968 p5581
      p17970 p2559
      (p18258 d203 (Eq.refl true))))

noncomputable def p18260 :=
@Enclosure.Real.IsNear.recentre' (@Inv.inv.{0} Real Real.instInv p17685) false
  1349831059 17179869184 1 17179869184 1349831059
  17179869184

noncomputable def p18261 :=
@Enclosure.Real.IsNear.inv_image p17685 218655440781 17179869184 41
  17179869184 674915529 674915530 8589934592
  (p17895 (Eq.refl true)) (Eq.refl true) (Eq.refl true)

noncomputable def p18262 :=
p17967
  (p18259
    (@p18260 1 17179869184
      (p18261 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (Eq.refl true))
    (Eq.refl true))

noncomputable def p18263 :=
@p17880 p17680
  (@p17882 8589934592
    (@p2563 1 0 1
      (BSN.neg_one_pow_even_mk 12 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1))
    p17898 (Eq.refl true))
  (p18262 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p18264 :=
@p17687 p15591 p17679 p17680
  (BSN.hardyZApproximantRS_eq
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
      true 5)
    12
    (p17688 (Eq.refl true) (Eq.refl true)
      (Eq.refl true)))
  (p17874 p18263 (Eq.refl true) (Eq.refl true))

theorem d236 : p17678 p17679 p17680 :=
@p17681 p15591 p17679 p17680
  (@Eq.refl.{1} Real
    (hardyZApproximantRS
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
        true 5)))
  p18264

theorem d237 : Enclosure.Real.IsNear Real.pi false 226375608064910080 72057594037927936 1
  1000000000000000 :=
BSN.pi_near_15

theorem d238 : p2306 500000000000000 :=
@p501 1 1000000000000000 884279719003555 140737488355328
  1 500000000000000 (Enclosure.Real.IsNear.const false 2 1)
  d237 (Eq.refl true)

noncomputable def p18265 :=
Enclosure.Real.IsNear
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi))
  false 179192535600709 1125899906842624

noncomputable def p18266 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
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
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 96 1)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi)))
  false 1188307408585

noncomputable def p18271 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 96 1)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi)))
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

noncomputable def p18274 :=
nat_lit
  116859913451098777154032399260620638157112902670295368528180643139215232358271105907355896346490890829979461579819176933559446339206796857465376087475828177446378591582584203219943350133140150208505

noncomputable def p18275 :=
nat_lit
  74751027079122046462216955587793573067050655862760405902609490213261724339546970300512875500623813013973275600053770769378323738155015176163371603062328757260320680744718580942157810765768356265984

noncomputable def p18276 :=
Enclosure.Real.IsNear
  (hardyZApproximantRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
      true 5))
  true p18274 p18275

noncomputable def p18277 :=
nat_lit
  64931332620426673616279147216430360307952349649185802269907920357855543529190041803638669155295792629434110060660109065803362488084659515102990544204742705626465590234451287206722980456139860294679510551816638702440439467498668169739776675179930631033

noncomputable def p18278 :=
nat_lit
  19554287803025706809171014015342734350243533643830549760181704902982984673037558563099253110863360877140577339680832398764194011523339780111728153586972816505922014655557161870950400000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p18279 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZApproximantRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
      true 5))
  (hardyZApproximantRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
      true 5))
  true p18274

noncomputable def p18280 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
  (Zeta.RiemannSiegel.mainSumOfPhase
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
      true 5)
    12)

noncomputable def p18281 :=
@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p18282 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (@HPow.hPow.{0, 0, 0} Real Nat Real
    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
    (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)))
    12)
  (p18281
    (@Neg.neg.{0} Real Real.instNeg
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
        (@OfNat.ofNat.{0} Real 4
          (@instOfNatAtLeastTwo.{0} Real 4 Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))))))

noncomputable def p18283 :=
Real.sqrt
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p18284 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p18282
  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
        (Enclosure.sfrac false 12 1)))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Zeta.RiemannSiegel.correctionLinear
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
          (Enclosure.sfrac false 12 1)))
      (@Inv.inv.{0} Real Real.instInv p18283)))

noncomputable def p18285 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZApproximantRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
      true 5))
  (p18280 p18284) true p18274

noncomputable def p18286 :=
@BSN.floor_sqrt_eq_dec
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
    true 5)
  101902800 100000 12
  (Enclosure.sfrac_ofScientific_eq 101902800 5 100000 (Eq.refl true))

noncomputable def p18287 :=
@Enclosure.Real.IsNear.subLit_tf
  (Zeta.RiemannSiegel.mainSumOfPhase
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
      true 5)
    12)

noncomputable def p18288 :=
nat_lit
  10156181745342544174971258077110851604735932507106245454095559134300968706474862621878217047516024407807661314961658389384216446190034753051242609967335745901277961594580463357104098356095759337465

noncomputable def p18289 :=
nat_lit
  2638272893960137795238961463308591470246259651917394790922047328092910840061380356907886906259030846078108388826175481413295571457498378639311978998885822976490812633491184806722980456139860294679510551816638702440439467498668169739776675179930631033

noncomputable def p18290 :=
nat_lit
  2007638025943438972568644437395120886189798506994198713955214066652704792335261419895383922563777041906672335348047434093101547595040460334917454992196468850589923377926960143983498335178056763720226224209920

noncomputable def p18291 :=
@p18287 p18284 24523491165 17179869184 54729
  17179869184 p18288 p18275 p18289
  p18278 p18290 p18274

noncomputable def p18292 :=
@Enclosure.Real.IsNear.of_eq
  (Zeta.RiemannSiegel.mainSumOfPhase
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
      true 5)
    12)

noncomputable def p18293 :=
@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
      true 5)
    12)

noncomputable def p18294 :=
p18293
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
      true 5)
    12)

noncomputable def p18295 :=
@p18292 p18294 true 24523491165 17179869184 54729
  17179869184
  (BSN.main_sum_of_phase_eq
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
      true 5)
    12)

noncomputable def p18296 :=
@Enclosure.Real.IsNear.addLit_tt
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
      true 5)
    12)

noncomputable def p18297 :=
@p18296
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
      true 5)
    12)

noncomputable def p18298 :=
@p18297 98093964660 137438953472 218916 137438953472
  98093964660 137438953472 218916 137438953472 26963863689579504599040
  24523491165 17179869184

noncomputable def p18299 :=
BSN.mainSumRS_step
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
      true 5))
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
    true 5)
  Real.cos BSN.quadSignNeg

noncomputable def p18300 :=
p18299 11 12 101902800 100000 286
  137438953472 68719476736 2305843009213693952 false 286267637457111
  3376

noncomputable def p18301 :=
p18300 341522969406 43 39675208392 8 true
  58517334207 205282 true 9690474853 7244019458077122842 1

noncomputable def p18302 :=
p18301 false 137097469473 true true 98093964660 218916
  BSN.abs_quadSignNeg (BSN.cos_quad_nat2 286 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 137097469473 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101902800 5 100000 (Eq.refl true))
  (Eq.refl true)

noncomputable def p18303 :=
BSN.mainSumRS_step2
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
      true 5))
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
    true 5)
  Real.sin Real.sin

noncomputable def p18304 :=
p18303 BSN.quadSignPos BSN.quadSignNeg 9 10 11 101902800
  100000 167 229 137438953472 68719476736

noncomputable def p18305 :=
p18304 2305843009213693952 false 286267637457111 3376
  316464885454 43 43462013224 8 329564216814 43
  41439403656

noncomputable def p18306 :=
p18305 8 true 65659019889 176109 true 165545090824
  true 129037125057 7244019458077122842 1 false

noncomputable def p18307 :=
p18306 128321242065 false false 110898162324 true true
  58517334207 205282 BSN.abs_quadSignPos
  (BSN.cos_quad_nat3 167 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 128321242065 137438953472)

noncomputable def p18308 :=
p18303 BSN.quadSignPos BSN.quadSignPos 7 8 9 101902800
  100000 23 99 137438953472 68719476736

noncomputable def p18309 :=
p18308 2305843009213693952 false 286267637457111 3376
  285796269294 43 48592008000 16 301984246446 43
  45812984488

noncomputable def p18310 :=
p18309 8 true 93974429095 143664 true 1325373751
  true 89793506300 7244019458077122842 1 false

noncomputable def p18311 :=
p18310 1325353208 false false 83540478263 false true
  65659019889 176109 BSN.abs_quadSignPos
  (BSN.cos_quad_nat3 23 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 1325353208 137438953472)

noncomputable def p18312 :=
p18303 BSN.quadSignPos BSN.quadSignPos 5 6 7 101902800
  100000 163 63 137438953472 68719476736

noncomputable def p18313 :=
p18312 2305843009213693952 false 286267637457111 3376
  246257546308 43 56109217800 8 267443854420 43
  51947041624

noncomputable def p18314 :=
p18313 8 true 183491059392 106539 false 134460224568
  false 133879369049 7244019458077122842 1 false

noncomputable def p18315 :=
p18314 114014442520 false false 113689068984 false true
  93974429095 143664 BSN.abs_quadSignPos
  (BSN.cos_quad_nat3 163 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 114014442520 137438953472)

noncomputable def p18316 :=
BSN.mainSumRS_step2
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
      true 5))
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
    true 5)
  Real.cos Real.sin

noncomputable def p18317 :=
p18316 BSN.quadSignNeg BSN.quadSignNeg 3 4 5 101902800
  100000 426 281 137438953472 68719476736

noncomputable def p18318 :=
p18317 2305843009213693952 false 286267637457111 3376
  190530846192 42 68719476728 8 221199462352 42
  61464568544

noncomputable def p18319 :=
p18318 16 true 87934555549 62773 false 142825329747
  false 194494215946 7244019458077122842 1 false

noncomputable def p18320 :=
p18319 69670243314 true false 135777138263 true true
  183491059392 106539 BSN.abs_quadSignNeg
  (BSN.cos_quad_nat2 426 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 69670243314 137438953472)

noncomputable def p18321 :=
p18316 BSN.quadSignPos BSN.quadSignNeg 1 2 3 101902800
  100000 876 613 137438953472 68719476736

noncomputable def p18322 :=
p18321 2305843009213693952 false 286267637457111 3376
  95265423088 42 97184016000 16 150992123216 42
  79350416784

noncomputable def p18323 :=
p18322 16 true 137437414144 3426 false 71087432011
  false 62722314604 7244019458077122842 1 false

noncomputable def p18324 :=
p18323 119460925530 false false 60567689668 true true
  87934555549 62773 BSN.abs_quadSignPos
  (BSN.cos_quad_nat0 876 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 119460925530 137438953472)

noncomputable def p18325 :=
@Enclosure.Real.IsNear.recentre'
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
      true 5)
    1)

noncomputable def p18326 :=
@Enclosure.Real.IsNear.of_eq
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
      true 5)
    1)

noncomputable def p18327 :=
@p18326
  (Real.cos
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
        true 5)))
  true 536864899

noncomputable def p18328 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
        true 5)))
  true 17179676768

noncomputable def p18329 :=
@Enclosure.Real.IsNear.cos_image
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
      true 5))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 17891727341069)
    (@Nat.cast.{0} Real Real.instNatCast 8589934592))
  false 17891727341069

noncomputable def p18330 :=
nat_lit 320545195329920285112051687374149701332872268821772323

noncomputable def p18331 :=
nat_lit 153895831809568121634589510752818082317481279488000

noncomputable def p18332 :=
@Enclosure.Real.IsNear.recentre'
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
      true 5))
  false p18330 p18331

noncomputable def p18333 :=
nat_lit 17301504000000000000000000

noncomputable def p18334 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 101902800 400000)
      (Real.log (Enclosure.sfrac false 41536732591360000 160000000000)))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 1 4)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 1 2) Real.pi)
        (Real.arctan
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@Nat.cast.{0} Real Real.instNatCast 100000)
            (@Nat.cast.{0} Real Real.instNatCast 203805600))))))

noncomputable def p18335 :=
nat_lit 527438817434312570367061982576640000000000000000

noncomputable def p18336 :=
nat_lit 3224849901828246877322219304683065835520000000000000

noncomputable def p18337 :=
@Enclosure.Real.IsNear.of_eq
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
      true 5))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (p18334 (Enclosure.sfrac false 101902800 200000))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 101902800 200000) (Real.log Real.pi)))
    (Enclosure.sfrac true p18335 p18336))
  false

noncomputable def p18338 :=
BSN.riemannSiegelThetaApproximant_two_zero_mk
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
    true 5)
  101902800 100000 41536732591360000 160000000000

noncomputable def p18339 :=
p18338 203805600 400000 200000 p18335
  p18336
  (Enclosure.sfrac_ofScientific_eq 101902800 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p18340 :=
@Enclosure.Real.IsNear.addLit_ft_p
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (p18334 (Enclosure.sfrac false 101902800 200000))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 101902800 200000) (Real.log Real.pi)))
  (Enclosure.sfrac true p18335 p18336) 9380418680778762712691
  4503599627370496000

noncomputable def p18341 :=
nat_lit 30250439886443984359348923912603275750233608493685286182584320000000000000

noncomputable def p18342 :=
@p18340 424903899692905601 p18333 p18335
  p18336 0 1 p18341 p18330
  p18331 424903899692905601 p18333

noncomputable def p18343 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (p18334 (Enclosure.sfrac false 101902800 200000))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 101902800 200000) (Real.log Real.pi))
  12007169748434340378227 4503599627370496000 160544586401 16500000000000000000

noncomputable def p18344 :=
nat_lit 322308731653857997298816713228288000

noncomputable def p18345 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 101902800 400000)
      (Real.log (Enclosure.sfrac false 41536732591360000 160000000000)))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 1 4)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 1 2) Real.pi)
        (Real.arctan
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@Nat.cast.{0} Real Real.instNatCast 100000)
            (@Nat.cast.{0} Real Real.instNatCast 203805600))))))

noncomputable def p18346 :=
@p18345 (Enclosure.sfrac false 101902800 200000)
  14301816808974391277171 4503599627370496000 160544586401 16500000000000000000
  101902800 200000 0

noncomputable def p18347 :=
nat_lit 2401433949686868075645400000

noncomputable def p18348 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 101902800 400000)
    (Real.log (Enclosure.sfrac false 41536732591360000 160000000000)))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 1 4)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 1 2) Real.pi)
      (Real.arctan
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@Nat.cast.{0} Real Real.instNatCast 100000)
          (@Nat.cast.{0} Real Real.instNatCast 203805600)))))
  14303584815974327091171

noncomputable def p18349 :=
nat_lit 32204828425809082364438572642921873408

noncomputable def p18350 :=
@p18348 4503599627370496000 106196389559 11000000000000000000
  884003499967907 2251799813685248 20000033 264000000000000000
  p18349 14301816808974391277171 4503599627370496000 160544586401

noncomputable def p18351 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 101902800 400000)
  (Real.log (Enclosure.sfrac false 41536732591360000 160000000000)) 101902800
  400000 0 1 56145993303321703 4503599627370496

noncomputable def p18352 :=
nat_lit 30866586245017820486659211264

noncomputable def p18353 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast 41536732591360000)
      (@Nat.cast.{0} Real Real.instNatCast 160000000000)))
  false p18352 p2333

noncomputable def p18354 :=
BSN.log_rat_reduce_isNear 41536732591360000 160000000000 17 83073465182720000
  41943040000000000 46963772185 68719476736 24973259072661432
  36028797018963968 26400000000 1000000000000000

noncomputable def p18355 :=
nat_lit
  1024780006508315234503144106111670720792570215136179720114539019559308519826559171523873949166396548755415893402517097414763158813597372888686518891193893637491372825813359541264542725130225602330403349340600158325722689292801704054225555988516660288043712469846997406136790568721259058692096000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p18356 :=
nat_lit
  39578491327462797563508018284557316000435740899529056709020583369099352543565554129627761753541040228649248255355706342693314668174347185897628558246303803335013833537297255415525040556894469590419588709116575432105854899383251254520565840753235218370297473292845720732305469002375692392857600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p18357 :=
nat_lit
  1064661123457785360591589388180155732982594401040443013613917018911483046638011022016381906013658462061830401389416083393785334220764825373518285257101038728103327730734674474999638580415468291316236003382596928001443803352370460227555851968465670677579142245803478131241073508352000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p18358 :=
BSN.log_dyadic_bound 20565212591360000 62508252591360000 12 11
  p18355 68719476736 26400000000 p18356 p18357
  46963772185 83073465182720000

noncomputable def p18359 :=
p18358 41943040000000000 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p18360 :=
@BSN.binarySplit_of_base11 (BSN.artanhP 20565212591360000) (BSN.artanhQ 62508252591360000)
  0 11 p18356 p18355 p18357
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p18361 :=
p18354 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p18359 (p18360 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

noncomputable def p18362 :=
@p18351 1250561 33000000000000000 14303584815974327091171
  4503599627370496000 106196389559 11000000000000000000
  (Enclosure.Real.IsNear.const false 101902800 400000)
  (BSN.isNear_log_sfrac 41536732591360000 160000000000 56145993303321703
    4503599627370496 1250561 33000000000000000 false
    (@p18353 1000448800000000 p2422 56145993303321703
      4503599627370496 1250561 33000000000000000
      (p18361 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p18363 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 1 4)
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 1 2) Real.pi)
    (Real.arctan
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@Nat.cast.{0} Real Real.instNatCast 100000)
        (@Nat.cast.{0} Real Real.instNatCast 203805600))))
  1 4

noncomputable def p18364 :=
@p18363 0 1 884003499967907 562949953421312 20000033
  66000000000000000 884003499967907 2251799813685248 20000033
  264000000000000000 (Enclosure.Real.IsNear.const false 1 4)

noncomputable def p18365 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 1 2) Real.pi)
  (Real.arctan
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast 100000) (@Nat.cast.{0} Real Real.instNatCast 203805600)))
  884279719003555 562949953421312 1

noncomputable def p18366 :=
nat_lit 7593532243823395229138944

noncomputable def p18367 :=
@p18365 2000000000000000 4214768 8589934592 1
  3300000000 p18366 884003499967907 562949953421312 20000033
  66000000000000000
  (@p803 1 1000000000000000 884279719003555 562949953421312
    1 2000000000000000 (Enclosure.Real.IsNear.const false 1 2)
    BSN.pi_near_15 (Eq.refl true))

noncomputable def p18368 :=
BSN.arctan_dyadic_bound_f 100000 203805600 1 0 8589934592
  3300000000 0 1 1 0 1

noncomputable def p18369 :=
p18368 1 4214768 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)
  (@BSN.binarySplit_of_le (BSN.arctanEvenP 100000) (BSN.arctanEvenQ 203805600) 0
    0 (Eq.refl true))
  (@BSN.binarySplit_of_le (BSN.arctanOddP 100000) (BSN.arctanOddQ 203805600) 0 0
    (Eq.refl true))

noncomputable def p18370 :=
p18364
  (p18367
    (p18369 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p18371 :=
@p18343 20040520230526563 34359738368000 254757 17179869184000
  p18344 9380418680778762712691 4503599627370496000 424903899692905601
  p18333
  (@p18346 1 p18347 12007169748434340378227
    4503599627370496000 160544586401 16500000000000000000
    (@p18350 16500000000000000000 p18362 p18370
      (Eq.refl true) (Eq.refl true))
    (Enclosure.Real.IsNear.const false 101902800 200000) (Eq.refl true)
    (Eq.refl true))

noncomputable def p18372 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 101902800 200000) (Real.log Real.pi)
  101902800 200000 0 1 78665238759 68719476736

noncomputable def p18373 :=
p18371
  (@p18372 1 34359738368 20040520230526563 34359738368000
    254757 17179869184000
    (Enclosure.Real.IsNear.const false 101902800 200000) d91
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p18374 :=
@p18329 8589934592 423 17179869184 true 17179676768
  17179869184 1 3300000000
  (@p18332 424903899692905601 p18333 17891727341069
    8589934592 423 17179869184
    (@p18337 p18330 p18331 424903899692905601
      p18333
      (p18339 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p18342 (p18373 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p18335 p18336)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p18375 :=
nat_lit 1938692645199642246059655168

noncomputable def p18376 :=
BSN.cos_reduce1
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 17891727341069)
    (@Nat.cast.{0} Real Real.instNatCast 8589934592))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast p18375)
    (@Nat.cast.{0} Real Real.instNatCast p2445))
  226375608064910080 72057594037927936 false

noncomputable def p18377 :=
BSN.sin_reduce_arg_pos_rat_q1 17891727341069 8589934592 226375608064910080
  72057594037927936 331 p18375 p2445
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p18378 :=
nat_lit
  1125634610566024956214575929087977583360608244286444787084647137267242979777204449808958819051988023338658375092705998894704268359236837758251993712737300106232247369140625

noncomputable def p18379 :=
nat_lit
  783267116538419746955661393207919532968365550560919972446039176907984572708746640576684843981364298440875991045568415754066674017108272699744950041830539703369140625

noncomputable def p18380 :=
nat_lit
  5621263133798587366646069273461970094472685576973127521190019190917574840252831326639878289284732111666913761679722475128811748094952395201414503751543190809002423369140625

noncomputable def p18381 :=
BSN.sin_dyadic_bound_f 55100959036725 35184372088832 4 3 17179869184
  6606445313 p18378 p3100 p18379
  p18380 p3103

noncomputable def p18382 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 55100959036725) (BSN.sinEvenQ 35184372088832) 0
  3 p18378 p3100 p18379 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p18383 :=
p18381 p18379 17179676768 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p18382 (Eq.refl true))

noncomputable def p18384 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 55100959036725) (BSN.sinOddQ 35184372088832) 0
  3 p18380 p3103 p18379 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p18385 :=
@BSN.sin_arg_round false 17179676768 17179869184 p18375
  p2445 55100959036725 35184372088832 6606445313 6600000000
  (p18383 (p18384 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p18386 :=
p18376 17179676768 17179869184 331 1000000000000000
  6600000000 3300000000 p18377 BSN.pi_near_15 p18385
  (Eq.refl true) (Eq.refl true)

noncomputable def p18387 :=
@p18327 536870912 5519843239 221459251200000000
  (BSN.main_sum_rs_one
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
      true 5))
  (@p18328 17179869184 1413079869184 56693568307200000000
    536864899 536870912 5519843239 221459251200000000
    (p18374 (Enclosure.sfrac_false_div 17891727341069 8589934592)
      (p18386 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p18388 :=
@p18325 true 536864899 536870912 5519843239
  221459251200000000 137437414144 137438953472 3426 137438953472
  p18387 (Eq.refl true)

noncomputable def p18389 :=
p18324 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 613 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 60567689668 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101902800 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true) p18388
  (@p18332 424903899692905601 p18333 286267637457111
    137438953472 3376 137438953472
    (@p18337 p18330 p18331 424903899692905601
      p18333
      (p18339 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p18342 (p18373 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p18335 p18336)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p18390 :=
nat_lit 15308704663048587253983145903992272722917204313753789352297684668690052887798369964214008161

noncomputable def p18391 :=
nat_lit 652142654883657420338081267711412837313549211792104022285257449568952553503100685334881

noncomputable def p18392 :=
nat_lit 45924809703835994447108761549441395343076985842837783848848483491171020758288103691271354721

noncomputable def p18393 :=
BSN.cos_dyadic_bound_f 71087432011 137438953472 3 2 137438953472
  68719476736 p18390 p2466 p18391
  p18392 p2469

noncomputable def p18394 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP 71087432011) (BSN.cosEvenQ 137438953472) 0
  2 p18390 p2466 p18391 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p18395 :=
p18393 p18391 119460925530 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p18394 (Eq.refl true))

noncomputable def p18396 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP 71087432011) (BSN.cosOddQ 137438953472) 0
  2 p18392 p2469 p18391 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p18397 :=
nat_lit 16699969595344608141281132130497078350163932439266677803580392854991749209189263802907033600

noncomputable def p18398 :=
nat_lit 239539209410058687726947749709551613026837713228877519514313700795597966698358977396736

noncomputable def p18399 :=
nat_lit 43737627781468262179765692902564246881151112937019880826726577159939007436882941188316921856

noncomputable def p18400 :=
BSN.sin_dyadic_bound_f 62722314604 137438953472 3 2 137438953472
  68719476736 p18397 p2477 p18398
  p18399 p2480

noncomputable def p18401 :=
@BSN.binarySplit_of_base2 (BSN.sinEvenP 62722314604) (BSN.sinEvenQ 137438953472) 0
  2 p18397 p2477 p18398 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p18402 :=
p18400 p18398 60567689668 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p18401 (Eq.refl true))

noncomputable def p18403 :=
@BSN.binarySplit_of_base2 (BSN.sinOddP 62722314604) (BSN.sinOddQ 137438953472) 0
  2 p18399 p2480 p18398 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p18404 :=
p18389 d93 d95 d97 d99 d103
  (p18395 (p18396 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p18402 (p18403 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p18405 :=
p18320 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 281 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 135777138263 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101902800 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p18404 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p18332 424903899692905601 p18333 286267637457111
    137438953472 3376 137438953472
    (@p18337 p18330 p18331 424903899692905601
      p18333
      (p18339 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p18342 (p18373 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p18335 p18336)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p18406 :=
nat_lit
  1058100170114800586506730063612252609971599090236803518865842531912369811555321379597372896639074859077218803897101653144935264366390703151921

noncomputable def p18407 :=
nat_lit
  72054784709243035869145940216229388182316466681788489684589129260277183643758156244546167760323057817258724240543633813540457203227441

noncomputable def p18408 :=
nat_lit
  6416172033640980624155169312043149708875490644018857769301581945278749928305907534011563438108516769791952597926564547688784650358049988795185

noncomputable def p18409 :=
BSN.cos_dyadic_bound_f 142825329747 137438953472 4 3 137438953472
  68719476736 p18406 p2457 p18407
  p18408 p2460

noncomputable def p18410 :=
@BSN.binarySplit_of_base3 (BSN.cosEvenP 142825329747) (BSN.cosEvenQ 137438953472) 0
  3 p18406 p2457 p18407 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p18411 :=
p18409 p18407 69670243314 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p18410 (Eq.refl true))

noncomputable def p18412 :=
@BSN.binarySplit_of_base3 (BSN.cosOddP 142825329747) (BSN.cosOddQ 137438953472) 0
  3 p18408 p2460 p18407 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p18413 :=
nat_lit
  9466299877552790391265490223288322722661928196827870874064950544478880977255051310181494729547744340110342402600027030869037260668201693679616

noncomputable def p18414 :=
nat_lit
  2930085442171559834626275391646605179183243540996758821184160877827658958918399197227454414193639990067551264002505261178867479310831616

noncomputable def p18415 :=
nat_lit
  47292735464394119307285368625098646235465501794385488759041031440728639708978974047866138159082913127951606162472448795124719210534273758334976

noncomputable def p18416 :=
BSN.sin_dyadic_bound_f 194494215946 137438953472 4 3 137438953472
  68719476736 p18413 p2504 p18414
  p18415 p2507

noncomputable def p18417 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 194494215946) (BSN.sinEvenQ 137438953472) 0
  3 p18413 p2504 p18414 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p18418 :=
p18416 p18414 135777138263 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p18417 (Eq.refl true))

noncomputable def p18419 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 194494215946) (BSN.sinOddQ 137438953472) 0
  3 p18415 p2507 p18414 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p18420 :=
p18405 d105 d107 d109 d111 d103
  (p18411 (p18412 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p18418 (p18419 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p18421 :=
p18315 BSN.abs_quadSignPos (BSN.cos_quad_nat3 63 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 113689068984 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101902800 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p18420 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p18332 424903899692905601 p18333 286267637457111
    137438953472 3376 137438953472
    (@p18337 p18330 p18331 424903899692905601
      p18333
      (p18339 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p18342 (p18373 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p18335 p18336)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p18422 :=
nat_lit
  2160153770153930538179904905229631526503885241852360861707944548824929519823803054433678051166085141818382404169190412055596068618716447768576

noncomputable def p18423 :=
nat_lit
  34924161434305687538445450599115777927328051414565156332998915581028179250998623495743619506649140670689530707631859002930505109733376

noncomputable def p18424 :=
nat_lit
  10798746653430990172210606471865481589323897157533095162039656474814467306439260114604018423297632189533094938283339185770696877616024975835136

noncomputable def p18425 :=
BSN.sin_dyadic_bound_f 134460224568 137438953472 4 3 137438953472
  68719476736 p18422 p2504 p18423
  p18424 p2507

noncomputable def p18426 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 134460224568) (BSN.sinEvenQ 137438953472) 0
  3 p18422 p2504 p18423 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p18427 :=
p18425 p18423 114014442520 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p18426 (Eq.refl true))

noncomputable def p18428 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 134460224568) (BSN.sinOddQ 137438953472) 0
  3 p18424 p2507 p18423 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p18429 :=
nat_lit
  2123057261992873958311112250535950253519731322065573856768371930487256579478559491904311600557506739266596480305999017780894769587246940349601

noncomputable def p18430 :=
nat_lit
  33156133774057654007765457011655140690422565551646089915586857263401970853629052681180977445807773379535498357403194785951447125386401

noncomputable def p18431 :=
nat_lit
  10613332952992858229471543482418772864114858226765558875423055754003092458890335375065823640926026648553061030802557522457751248322142025344161

noncomputable def p18432 :=
BSN.sin_dyadic_bound_f 133879369049 137438953472 4 3 137438953472
  68719476736 p18429 p2504 p18430
  p18431 p2507

noncomputable def p18433 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 133879369049) (BSN.sinEvenQ 137438953472) 0
  3 p18429 p2504 p18430 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p18434 :=
p18432 p18430 113689068984 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p18433 (Eq.refl true))

noncomputable def p18435 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 133879369049) (BSN.sinOddQ 137438953472) 0
  3 p18431 p2507 p18430 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p18436 :=
p18421 d113 d115 d117 d119 d103
  (p18427 (p18428 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p18434 (p18435 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p18437 :=
p18311 BSN.abs_quadSignPos (BSN.cos_quad_nat3 99 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 83540478263 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101902800 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p18436 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p18332 424903899692905601 p18333 286267637457111
    137438953472 3376 137438953472
    (@p18337 p18330 p18331 424903899692905601
      p18333
      (p18339 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p18342 (p18373 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p18335 p18336)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p18438 :=
BSN.sin_dyadic_bound_f 1325373751 137438953472 1 0 137438953472
  68719476736 0 1 1 0 1

noncomputable def p18439 :=
p18438 1 1325353208 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (@BSN.binarySplit_of_le (BSN.sinEvenP 1325373751) (BSN.sinEvenQ 137438953472) 0
    0 (Eq.refl true))

noncomputable def p18440 :=
p18439
  (@BSN.binarySplit_of_le (BSN.sinOddP 1325373751) (BSN.sinOddQ 137438953472) 0
    0 (Eq.refl true))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p18441 :=
nat_lit 70149896139105425081392367475377032495896613577871447610905893972723875068373408998400000000

noncomputable def p18442 :=
nat_lit 4226291452346008299654638978690884511216801053592073612049598438414275210000000000000000

noncomputable def p18443 :=
nat_lit 183719075892448505485447235877164823676234875026052737528429261054900335400161785472000000000

noncomputable def p18444 :=
BSN.sin_dyadic_bound_f 89793506300 137438953472 3 2 137438953472
  68719476736 p18441 p2477 p18442
  p18443 p2480

noncomputable def p18445 :=
@BSN.binarySplit_of_base2 (BSN.sinEvenP 89793506300) (BSN.sinEvenQ 137438953472) 0
  2 p18441 p2477 p18442 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p18446 :=
p18444 p18442 83540478263 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p18445 (Eq.refl true))

noncomputable def p18447 :=
@BSN.binarySplit_of_base2 (BSN.sinOddP 89793506300) (BSN.sinOddQ 137438953472) 0
  2 p18443 p2480 p18442 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p18448 :=
p18437 d121 d123 d125 d127 d103
  p18440
  (p18446 (p18447 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true) (Eq.refl true)

noncomputable def p18449 :=
p18307 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 229 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 110898162324 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101902800 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p18448 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true))
  (@p18332 424903899692905601 p18333 286267637457111
    137438953472 3376 137438953472
    (@p18337 p18330 p18331 424903899692905601
      p18333
      (p18339 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p18342 (p18373 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p18335 p18336)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p18450 :=
nat_lit
  4965297077286301295170572822256202203731763516895671917304595756060954417586919747763985849566899502811456404055616006159384115668021386674176

noncomputable def p18451 :=
nat_lit
  423638749407225841258300236547058302693490180334688343418067712457678809552850932158186665698833559851115888481796750856070761310846976

noncomputable def p18452 :=
nat_lit
  24815808558122721547527885818404483363173107020411510260871810394508522919431805216396697258709067834872863325646523129307728434246578639732736

noncomputable def p18453 :=
BSN.sin_dyadic_bound_f 165545090824 137438953472 4 3 137438953472
  68719476736 p18450 p2504 p18451
  p18452 p2507

noncomputable def p18454 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 165545090824) (BSN.sinEvenQ 137438953472) 0
  3 p18450 p2504 p18451 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p18455 :=
p18453 p18451 128321242065 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p18454 (Eq.refl true))

noncomputable def p18456 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 165545090824) (BSN.sinOddQ 137438953472) 0
  3 p18452 p2507 p18451 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p18457 :=
nat_lit
  1832095383611702917616770640861429099979100166859293200714518131629415373085458581923490716522449660001003927425667370723731338201459020883201

noncomputable def p18458 :=
nat_lit
  21309641381284135921505430422811798221787001385150292807229223682005745745894765571213320755397006728265088693610158416432130171168001

noncomputable def p18459 :=
nat_lit
  9159022176825259542788777781876795947047067685812790862170477426351079255460573635250920963329858028044514793547557487549773126551786244629761

noncomputable def p18460 :=
BSN.sin_dyadic_bound_f 129037125057 137438953472 4 3 137438953472
  68719476736 p18457 p2504 p18458
  p18459 p2507

noncomputable def p18461 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 129037125057) (BSN.sinEvenQ 137438953472) 0
  3 p18457 p2504 p18458 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p18462 :=
p18460 p18458 110898162324 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p18461 (Eq.refl true))

noncomputable def p18463 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 129037125057) (BSN.sinOddQ 137438953472) 0
  3 p18459 p2507 p18458 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p18464 :=
p18449 d129 d131 d133 d135 d103
  (p18455 (p18456 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p18462 (p18463 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p18465 :=
p18302
  (p18464 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p18332 424903899692905601 p18333 286267637457111
    137438953472 3376 137438953472
    (@p18337 p18330 p18331 424903899692905601
      p18333
      (p18339 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p18342 (p18373 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p18335 p18336)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p18466 :=
nat_lit 8818205908350745292082783984617343248881

noncomputable def p18467 :=
BSN.cos_dyadic_bound_f 9690474853 137438953472 2 1 137438953472
  68719476736 p18466 p2486 p18466
  p18466 p2487

noncomputable def p18468 :=
@BSN.binarySplit_of_base (BSN.cosEvenP 9690474853) (BSN.cosEvenQ 137438953472) 0
  1 p18466 p2486 p18466 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p18469 :=
p18467 p18466 137097469473 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p18468 (Eq.refl true))

noncomputable def p18470 :=
@BSN.binarySplit_of_base (BSN.cosOddP 9690474853) (BSN.cosOddQ 137438953472) 0 1
  p18466 p2487 p18466 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p18471 :=
p18465 d137 d139 d103
  (p18469 (p18470 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true) (Eq.refl true)

noncomputable def p18472 :=
@p18291 p18275 p18277 p18278
  (p18295
    (@p18298 54729 17179869184
      (p18471 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (p18471 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true) (Eq.refl true)))

noncomputable def p18473 :=
@Enclosure.Real.IsNear.mulLit_ff p18282
  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
        (Enclosure.sfrac false 12 1)))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Zeta.RiemannSiegel.correctionLinear
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
          (Enclosure.sfrac false 12 1)))
      (@Inv.inv.{0} Real Real.instInv p18283)))

noncomputable def p18474 :=
nat_lit
  2109658567595044498248110007902919084780512286053728967070981900842641672493037545965909044753369970431647571745577468306516729473893090231058762285998630899147077748330169507017590464355

noncomputable def p18475 :=
nat_lit
  4351082437154956072465106588077822995084026820419845514849846380137705962380101572519219218556758308199541387151331336317719177934050977705242787666055883587123865770683541250307916824576

noncomputable def p18476 :=
nat_lit
  547911695053384696617986008487750889927466644520695237882163428199806307548952098884356887201092544396573391367595471103332780619129663533644059325543604216639029512392615874048723096166583931755746397762952561936269976814500769689769853637

noncomputable def p18477 :=
nat_lit
  1138209353842871892799798749349006355637890149596528485427942645211179314241602467553413770561069301163112822668675356472620857618943542481384249030785449809972314085785600000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p18478 :=
@p18473 4814135283 17179869184 1 17179869184
  p18474 p18475 p18476 p18477
  p18288 p18275 p18289

noncomputable def p18479 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HPow.hPow.{0, 0, 0} Real Nat Real
    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
    (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)))
    12)
  (p18281
    (@Neg.neg.{0} Real Real.instNeg
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
        (@OfNat.ofNat.{0} Real 4
          (@instOfNatAtLeastTwo.{0} Real 4 Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))))))

noncomputable def p18480 :=
@p18479 1 1 0 1 4814135283 17179869184
  1 17179869184 4814135283 17179869184 1

noncomputable def p18481 :=
@Enclosure.Real.IsNear.of_eq
  (p18281
    (@Neg.neg.{0} Real Real.instNeg
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
        (@OfNat.ofNat.{0} Real 4
          (@instOfNatAtLeastTwo.{0} Real 4 Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))))))

noncomputable def p18482 :=
BSN.rpow_neg_quarter_mk
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p18483 :=
p18482
  (BSN.t_div_two_pi_nonneg
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
      true 5)
    101902800 100000
    (Enclosure.sfrac_ofScientific_eq 101902800 5 100000 (Eq.refl true)))

noncomputable def p18484 :=
@Enclosure.Real.IsNear.recentre' (@Inv.inv.{0} Real Real.instInv (Real.sqrt p18283)) false
  4814135283 17179869184 1 17179869184 4814135283
  17179869184

noncomputable def p18485 :=
@Enclosure.Real.IsNear.recentre' (Real.sqrt p18283) false 61308602238
  17179869184 6 17179869184 30654301119 8589934592 3
  8589934592

noncomputable def p18486 :=
@Enclosure.Real.IsNear.sqrt_image
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p18487 :=
@Enclosure.Real.IsNear.of_eq
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p18488 :=
@p18487
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 101902800 100000)
    (@Inv.inv.{0} Real Real.instInv
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)))
  false 696572155816971

noncomputable def p18489 :=
@p18488 4294967296000 254757 4294967296000
  (BSN.t_div_two_pi_mk
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
      true 5)
    101902800 100000
    (Enclosure.sfrac_ofScientific_eq 101902800 5 100000 (Eq.refl true)))

noncomputable def p18490 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 101902800 100000)
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi))
  101902800 100000 0

noncomputable def p18491 :=
@p18490 1 2734261103 17179869184 1 17179869184
  696572155816971 4294967296000 254757 4294967296000
  (Enclosure.Real.IsNear.const false 101902800 100000) d142

noncomputable def p18492 :=
@p18486 696572155816971 4294967296000 254757 4294967296000
  109393868702 109393868743 8589934592
  (p18489 (p18491 (Eq.refl true))) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p18493 :=
@Enclosure.Real.IsNear.recentre' p18283 false 218787737445 17179869184
  41 17179869184 218787737445 17179869184 41 17179869184
  (p18492 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p18494 :=
@Enclosure.Real.IsNear.sqrt_image p18283 218787737445 17179869184 41
  17179869184 30654301116 30654301122 8589934592
  (p18493 (Eq.refl true)) (Eq.refl true) (Eq.refl true)

noncomputable def p18495 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt p18283) 30654301119 8589934592
  3 8589934592 2407067641 2407067642 8589934592
  (p18485
    (p18494 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p18496 :=
@p18481 (@Inv.inv.{0} Real Real.instInv (Real.sqrt p18283)) false
  4814135283 17179869184 1 17179869184 p18483
  (@p18484 1 17179869184
    (p18495 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p18497 :=
@Enclosure.Real.IsNear.addLit_ft_p
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
      (Enclosure.sfrac false 12 1)))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Zeta.RiemannSiegel.correctionLinear
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
        (Enclosure.sfrac false 12 1)))
    (@Inv.inv.{0} Real Real.instInv p18283))
  35835617053588126845

noncomputable def p18498 :=
nat_lit
  3501936007074663911123990866211187624233752343764508103300509904225108864486084359332199850432191503866889197444288599423672969745722396021088607892734923017577748334129831756474196125

noncomputable def p18499 :=
nat_lit
  1353793303521911519324599847533747985519642983697399082341438466220401159170044234710653962675419282427437499176390945917158441191336480865094293050333651548539243876263874048723096166583931755746397762952561936269976814500769689769853637

noncomputable def p18500 :=
nat_lit
  155665326717337874432299564916236045646507154105554235522969300804281999888693582580957901083400417169799800318752884718080533040751837996738692382794570934383784799750228328154669527521360674689297122590720

noncomputable def p18501 :=
@p18497 73786976294838206464 41521690823795674919 p15814
  p18498 p18475 p18499 p18477
  p18500 p18474 p18475 p18476

noncomputable def p18502 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (@Inv.inv.{0} Real Real.instInv
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
          (Enclosure.sfrac false 12 1)))))

noncomputable def p18503 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
        (Enclosure.sfrac false 12 1))
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
        (Enclosure.sfrac false 12 1)))
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
      (Enclosure.sfrac false 12 1)))

noncomputable def p18504 :=
@Enclosure.Real.IsNear.of_eq
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
      (Enclosure.sfrac false 12 1)))
  (p18502
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p18503 (Enclosure.sfrac false 1 16)))))

noncomputable def p18505 :=
BSN.cos_two_pi_p_ne_zero_mk
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
    true 5)
  101902800 100000 12
  (Enclosure.sfrac_ofScientific_eq 101902800 5 100000 (Eq.refl true))

noncomputable def p18506 :=
@Enclosure.Real.IsNear.mulLit_tt
  (@Inv.inv.{0} Real Real.instInv
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
          (Enclosure.sfrac false 12 1)))))

noncomputable def p18507 :=
@p18506
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p18503 (Enclosure.sfrac false 1 16))))
  92026045307

noncomputable def p18508 :=
@p18507 8589934592 15105 8589934592 389407335
  8589934592 8278436989 221459251200000000 35835617053588126845
  73786976294838206464 41521690823795674919 p15814

noncomputable def p18509 :=
@Enclosure.Real.IsNear.of_eq
  (@Inv.inv.{0} Real Real.instInv
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
          (Enclosure.sfrac false 12 1)))))

noncomputable def p18510 :=
@Inv.inv.{0} Real Real.instInv
  (@Neg.neg.{0} Real Real.instNeg
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
          (Enclosure.sfrac false 12 1)))))

noncomputable def p18511 :=
@p18509 (@Neg.neg.{0} Real Real.instNeg p18510) true 92026045307
  8589934592 15105 8589934592
  (BSN.inv_eq_neg_inv_neg
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
          (Enclosure.sfrac false 12 1)))))

noncomputable def p18512 :=
@Enclosure.Real.IsNear.inv_image
  (@Neg.neg.{0} Real Real.instNeg
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
          (Enclosure.sfrac false 12 1)))))

noncomputable def p18513 :=
@Enclosure.Real.IsNear.neg
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
        (Enclosure.sfrac false 12 1))))
  true

noncomputable def p18514 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
        (Enclosure.sfrac false 12 1))))
  true

noncomputable def p18515 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
      (Enclosure.sfrac false 12 1)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 79352277671)
    (@Nat.cast.{0} Real Real.instNatCast 17179869184))
  false

noncomputable def p18516 :=
nat_lit 11167840254743923590227535

noncomputable def p18517 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
      (Enclosure.sfrac false 12 1)))
  false p18516

noncomputable def p18518 :=
nat_lit 1106429200255728971764169951

noncomputable def p18519 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
    (Enclosure.sfrac false 12 1))
  884279719003555 140737488355328 1

noncomputable def p18520 :=
@Enclosure.Real.IsNear.subLit_ff_p p18283 (Enclosure.sfrac false 12 1)
  218787737445 17179869184 41 17179869184 12 1 0

noncomputable def p18521 :=
@p18519 500000000000000 12629307237 17179869184 41
  17179869184 p18516 p2602 p18518
  p5018 d141
  (@p18520 1 12629307237 12629307237 17179869184 41
    17179869184 (p18493 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p18522 :=
@p18515 79352277671 17179869184 129 8589934592 true
  1603610718 17179869184 1 3300000000
  (@p18517 p2602 p18518 p5018
    79352277671 17179869184 129 8589934592
    (p18521 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div 79352277671 17179869184)

noncomputable def p18523 :=
nat_lit 3657661754796482255673884672

noncomputable def p18524 :=
BSN.cos_reduce2
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 79352277671)
    (@Nat.cast.{0} Real Real.instNatCast 17179869184))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast p18523)
    (@Nat.cast.{0} Real Real.instNatCast p2333))
  226375608064910080 72057594037927936 false

noncomputable def p18525 :=
BSN.sin_reduce_arg_pos_rat_q2 79352277671 17179869184 226375608064910080
  72057594037927936 0 p18523 p2333 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p18526 :=
nat_lit
  343122497132905727557796448211857340962075275497475037018291439518393521138352661414619012040912045251926843471262311642165015710115758984637153765872833282834519843433361

noncomputable def p18527 :=
nat_lit
  388942040842991150351553744139598477515736646995524489247203009274540057369958693243971801303191265174229337204339640214851457026197289810080579580368762975440366481

noncomputable def p18528 :=
nat_lit
  2077684428384593790452879346136501463506740095958845490102305165937057614640044499745974224495123430213583142640749901568089501745723693036293982268352375786470553847622545

noncomputable def p18529 :=
BSN.cos_dyadic_bound_f 51978499794763 35184372088832 4 3 17179869184
  6606445313 p18526 p2613 p18527
  p18528 p2616

noncomputable def p18530 :=
@BSN.binarySplit_of_base3 (BSN.cosEvenP 51978499794763) (BSN.cosEvenQ 35184372088832) 0
  3 p18526 p2613 p18527 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p18531 :=
p18529 p18527 1603610718 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p18530 (Eq.refl true))

noncomputable def p18532 :=
@BSN.binarySplit_of_base3 (BSN.cosOddP 51978499794763) (BSN.cosOddQ 35184372088832) 0
  3 p18528 p2616 p18527 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p18533 :=
@BSN.cos_arg_round false 1603610718 17179869184 p18523
  p2333 51978499794763 35184372088832 6606445313 6600000000
  (p18531 (p18532 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p18534 :=
p18524 1603610718 17179869184 0 1000000000000000
  6600000000 3300000000 p18525 BSN.pi_near_15 p18533
  (Eq.refl true) (Eq.refl true)

noncomputable def p18535 :=
@p18513 801805359 8589934592 1696445057 110729625600000000
  (@p18514 1603610718 17179869184 434289934592
    28346784153600000000 801805359 8589934592 1696445057
    110729625600000000
    (p18522 (p18534 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p18536 :=
@p18512 801805359 8589934592 1696445057 110729625600000000
  92026030202 92026060412 8589934592 p18535
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p18537 :=
@Enclosure.Real.IsNear.recentre' p18510 false 184052090614 17179869184
  30210 17179869184 92026045307 8589934592 15105 8589934592
  (p18536 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p18538 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p18503 (Enclosure.sfrac false 1 16))))
  true

noncomputable def p18539 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p18503 (Enclosure.sfrac false 1 16)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Neg.neg.{0} Real Real.instNeg (@Nat.cast.{0} Real Real.instNatCast 3470644635))
    (@Nat.cast.{0} Real Real.instNatCast 2147483648))
  true

noncomputable def p18540 :=
nat_lit 67132030559442860684959555202605525

noncomputable def p18541 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p18503 (Enclosure.sfrac false 1 16)))
  true p18540

noncomputable def p18542 :=
nat_lit 46955173627338407636590039295170832813

noncomputable def p18543 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (p18503 (Enclosure.sfrac false 1 16)) 884279719003555
  140737488355328 1

noncomputable def p18544 :=
@Enclosure.Real.IsNear.subLit_tf
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
        (Enclosure.sfrac false 12 1))
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
        (Enclosure.sfrac false 12 1)))
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
      (Enclosure.sfrac false 12 1)))

noncomputable def p18545 :=
@p18544 (Enclosure.sfrac false 1 16) 57470444929663910439
  295147905179352825856 1739977831659 295147905179352825856 1 16
  0

noncomputable def p18546 :=
@Enclosure.Real.IsNear.subLit_ff_n
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
      (Enclosure.sfrac false 12 1))
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
      (Enclosure.sfrac false 12 1)))
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
    (Enclosure.sfrac false 12 1))
  159499401286540574169

noncomputable def p18547 :=
nat_lit 987334725837902062427912011776

noncomputable def p18548 :=
@p18546 295147905179352825856 1035603195115 295147905179352825856
  12629307237 17179869184 41 17179869184 p18547
  57470444929663910439 295147905179352825856 1739977831659

noncomputable def p18549 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
    (Enclosure.sfrac false 12 1))
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
    (Enclosure.sfrac false 12 1))
  12629307237 17179869184 41

noncomputable def p18550 :=
@p18549 17179869184 12629307237 17179869184 41
  17179869184 159499401286540574169 295147905179352825856 1035603195115
  295147905179352825856
  (@p18520 1 12629307237 12629307237 17179869184 41
    17179869184 (p18493 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p18551 :=
p18550
  (@p18520 1 12629307237 12629307237 17179869184 41
    17179869184 (p18493 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p18552 :=
@p18548 295147905179352825856 (p18551 (Eq.refl true))
  (@p18520 1 12629307237 12629307237 17179869184 41
    17179869184 (p18493 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p18553 :=
@p18543 500000000000000 75917189003373462055 295147905179352825856
  1739977831659 295147905179352825856 p18540 p2630
  p18542 p2632 d141
  (@p18545 1 1214675024053975392880 75917189003373462055
    295147905179352825856 1739977831659 295147905179352825856
    (p18552 (Eq.refl true) (Eq.refl true))
    (Enclosure.Real.IsNear.const false 1 16) (Eq.refl true)
    (Eq.refl true))

noncomputable def p18554 :=
@p18539 3470644635 2147483648 637 17179869184 true
  389407335 8589934592 1 3300000000
  (@p18541 p2630 p18542 p2632
    3470644635 2147483648 637 17179869184
    (p18553 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_true_div 3470644635 2147483648)

noncomputable def p18555 :=
nat_lit
  1221710628400299466478686754116808327023373022131844959065384351615873776622339963202532796174353077202421275324983272426362286677901948359060339482710687107890625

noncomputable def p18556 :=
nat_lit
  443161848453473356109691531182976376104464964959876562905092064235374199112079577359447686873680243391586526176643310133968480532015321348047027587890625

noncomputable def p18557 :=
nat_lit
  12427825100014684399109809263358858188947632153814547485120746410034250987096055807776742798501928339970007896888179443015090279635362811392094775376666082691890625

noncomputable def p18558 :=
BSN.cos_dyadic_bound_t 3470644635 2147483648 5 4 8589934592
  3300000000 p18555 p15874 p18556
  p18557 p15877

noncomputable def p18559 :=
@BSN.binarySplit_of_base4 (BSN.cosEvenP 3470644635) (BSN.cosEvenQ 2147483648) 0
  4 p18555 p15874 p18556 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p18560 :=
p18558 p18556 389407335 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p18559 (Eq.refl true))

noncomputable def p18561 :=
@BSN.binarySplit_of_base4 (BSN.cosOddP 3470644635) (BSN.cosOddQ 2147483648) 0 4
  p18557 p15877 p18556 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p18562 :=
p18554
  (BSN.cos_neg_of_bound 3470644635 2147483648 true 389407335 8589934592
    1 3300000000
    (p18560 (p18561 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p18563 :=
p18508
  (p18511
    (@Enclosure.Real.IsNear.neg p18510 false 92026045307 8589934592
      15105 8589934592 (p18537 (Eq.refl true))))
  (@p18538 389407335 8589934592 2119279869184
    56693568307200000000 389407335 8589934592 8278436989
    221459251200000000 (p18562 (Eq.refl true)) (Eq.refl true))

noncomputable def p18564 :=
@p18501 p18477
  (@p18504 false 35835617053588126845 73786976294838206464
    41521690823795674919 p15814
    (BSN.correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
        (Enclosure.sfrac false 12 1))
      (p18505 (Eq.refl true) (Eq.refl true)
        (p18286 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p18563 (Eq.refl true)))

noncomputable def p18565 :=
nat_lit
  2595921034706260760634188860597427558648257470481003523917868340478377423224604474816886688942229454673901758873596470445709521185544432160920714119032805199147648173156410375

noncomputable def p18566 :=
nat_lit
  253266331108459042877954581524118722595974501479640924072000569439126758509088631982403994686712878069348015540240526683495797795130113239006767262824338603946605334680267915264

noncomputable def p18567 :=
@Enclosure.Real.IsNear.mulLit_tf
  (Zeta.RiemannSiegel.correctionLinear
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
      (Enclosure.sfrac false 12 1)))
  (@Inv.inv.{0} Real Real.instInv p18283) p18565 p18566

noncomputable def p18568 :=
nat_lit
  1003038800329027153016602275746263161960142753103309515555106855791537587647518751244276188617594582512419855509372452528241380672484880963448257937723319122088403601816995388425783382143101730829281388241172887187649106533798923

noncomputable def p18569 :=
nat_lit
  66252504117022727895516363749571980188943570805511465612097098795416492167953545434482731539818301166123292797051565516310561076909277034072685581095601071718400000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p18570 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
      (Enclosure.sfrac false 12 1)))
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 96 1)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi)))

noncomputable def p18571 :=
@Enclosure.Real.IsNear.of_eq
  (Zeta.RiemannSiegel.correctionLinear
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
      (Enclosure.sfrac false 12 1)))
  (@Neg.neg.{0} Real Real.instNeg p18570) true p18565

noncomputable def p18572 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
      (Enclosure.sfrac false 12 1)))
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 96 1)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi)))

noncomputable def p18573 :=
nat_lit
  2184553437899881374351205135802681585406466424232054156934210292049163428572889843586455307568151674559394002579802968742011565808119296150319821847896541446224975

noncomputable def p18574 :=
nat_lit
  224945689727159819140526925384299092943484855915095831655037778630591879033574393515952034305194542857496045531676044756160413302774714984450425759043258192756736

noncomputable def p18575 :=
nat_lit
  844089855553763436871096128262396228307918093216739154707744132817116490711845548496616589618582868085894009282888464726454380926696991210118261304017710497459820242367467416568829086340184062707692115039206925156893

noncomputable def p18576 :=
nat_lit
  58844044407833287287271740728275642052963308619616591965326345455104199693566564941067592844186774284519086106338972467276137014477368078211481600000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p18577 :=
@p18572 p18573 p18574 p18575
  p18576 1188307408585 1125899906842624 1 1125899906842624
  p18565 p18566 p18568

noncomputable def p18578 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p18579 :=
p18578
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p18580 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p18579
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p18581 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p18580
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p18503 (Enclosure.sfrac false 1 16)))))

noncomputable def p18582 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (Enclosure.sfrac false 3 1)
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p18583 :=
p18581
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p18582
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 4 1) Real.pi))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p18503 (Enclosure.sfrac false 1 16)))))

noncomputable def p18584 :=
@Neg.neg.{0} Real Real.instNeg
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
          (Enclosure.sfrac false 12 1)))))

noncomputable def p18585 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18583
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 3 1) p18584)
    (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
        (Enclosure.sfrac false 12 1))))

noncomputable def p18586 :=
@Neg.neg.{0} Real Real.instNeg
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 4 1)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
          (Enclosure.sfrac false 12 1)))))

noncomputable def p18587 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18585
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 3 1) p18586)
    (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
        (Enclosure.sfrac false 12 1))))

noncomputable def p18588 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 8 1)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi) Real.pi))
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
        (Enclosure.sfrac false 12 1))))

noncomputable def p18589 :=
@Enclosure.Real.IsNear.of_eq
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
      (Enclosure.sfrac false 12 1)))
  (p18502
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18587
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p18588
        (Zeta.RiemannSiegel.correction
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
            (Enclosure.sfrac false 12 1))))))

noncomputable def p18590 :=
@p18506
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18587
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p18588
      (Zeta.RiemannSiegel.correction
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
          (Enclosure.sfrac false 12 1)))))
  12062036528998723

noncomputable def p18591 :=
nat_lit
  181109834367349780027323629859633670628705254556060631338540558441993319291333101968853301251626967297596079947756390925460183600089900606930680325

noncomputable def p18592 :=
nat_lit
  199791907220223502808422222706762643567910281130558153654986045416023791284464999687699590596063486154228923591770023865308670443474450259602571264

noncomputable def p18593 :=
nat_lit
  17494732573063115660249833786759948760290351093891893344585976219301856266658299808821759517170152938009922720584271778960265595640017076621968940028427793374780105844072537142914337463189082031856941

noncomputable def p18594 :=
nat_lit
  13066002592728340145294239233625531072072358500428055797587833065676976505812626459205903560564626505362336962598795435059026329600000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p18595 :=
@p18590 1125899906842624 30439 1125899906842624 p18591
  p18592 p18593 p18594 p18573
  p18574 p18575 p18576

noncomputable def p18596 :=
@p18509 (@Neg.neg.{0} Real Real.instNeg p18510) true
  12062036528998723 1125899906842624 30439 1125899906842624
  (BSN.inv_eq_neg_inv_neg
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
          (Enclosure.sfrac false 12 1)))))

noncomputable def p18597 :=
nat_lit 60874255443241520332800000000

noncomputable def p18598 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
      (Enclosure.sfrac false 12 1)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 5200430858322971)
    (@Nat.cast.{0} Real Real.instNatCast 1125899906842624))
  false

noncomputable def p18599 :=
nat_lit 731895577365917618141987086595

noncomputable def p18600 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
      (Enclosure.sfrac false 12 1)))
  false p18599

noncomputable def p18601 :=
nat_lit 222707751935275461099434643

noncomputable def p18602 :=
nat_lit 967140655691703339764940800000000000000

noncomputable def p18603 :=
@Enclosure.Real.IsNear.subLit_ff_p p18283 (Enclosure.sfrac false 12 1)
  14338473159421217 1125899906842624 41 1125899906842624 12
  1 0

noncomputable def p18604 :=
@p18487
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 101902800 100000)
    (@Inv.inv.{0} Real Real.instInv
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)))
  false 45650552792029822713

noncomputable def p18605 :=
@p18604 281474976710656000 254757 281474976710656000
  (BSN.t_div_two_pi_mk
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
      true 5)
    101902800 100000
    (Enclosure.sfrac_ofScientific_eq 101902800 5 100000 (Eq.refl true)))

noncomputable def p18606 :=
@p18490 1 179192535600709 1125899906842624 1
  1125899906842624 45650552792029822713 281474976710656000 254757
  281474976710656000 (Enclosure.Real.IsNear.const false 101902800 100000)
  d239

noncomputable def p18607 :=
@p18486 45650552792029822713 281474976710656000 254757
  281474976710656000 7169236579710588 7169236579710629 562949953421312
  (p18605 (p18606 (Eq.refl true))) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p18608 :=
@Enclosure.Real.IsNear.recentre' p18283 false 14338473159421217
  1125899906842624 41 1125899906842624 14338473159421217
  1125899906842624 41 1125899906842624
  (p18607 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p18609 :=
@p18519 500000000000000 827674277309729 1125899906842624 41
  1125899906842624 p18599 p3344 p18601
  p18602 d238
  (@p18603 1 827674277309729 827674277309729 1125899906842624
    41 1125899906842624 (p18608 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p18610 :=
@p18598 5200430858322971 1125899906842624 65 281474976710656
  true 105094243180298 1125899906842624 1 216268800000000
  (@p18600 p3344 p18601 p18602
    5200430858322971 1125899906842624 65 281474976710656
    (p18609 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div 5200430858322971 1125899906842624)

noncomputable def p18611 :=
nat_lit 239708519159250305236266880335872

noncomputable def p18612 :=
nat_lit 162259276829213363391578010288128

noncomputable def p18613 :=
BSN.cos_reduce2
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 5200430858322971)
    (@Nat.cast.{0} Real Real.instNatCast 1125899906842624))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast p18611)
    (@Nat.cast.{0} Real Real.instNatCast p18612))
  226375608064910080 72057594037927936 false

noncomputable def p18614 :=
BSN.sin_reduce_arg_pos_rat_q2 5200430858322971 1125899906842624 226375608064910080
  72057594037927936 0 p18611 p18612
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p18615 :=
nat_lit
  8742464683774729376237350525833198147111445857941238148449482916433734095156639487803371032913421760998670348139704379096934696185163023271228268272894641740748790390732539488459039201888837332708590256732004536859449023664100313769061646969159540814540233408497801403972476853972165085668135735551385747092843355858228531209405831197031465686419338388205473851931044786944328394080256

noncomputable def p18616 :=
nat_lit
  43925764306044571680725368323646467224816202519423813658702209381811720879245495124946621119333294851884583971973988952045017884473517666335936773745853447711512838489228428960142291910923747779038711709484005529634972877481305336765315945935580498848143981594566316233845365667885724853864409164021094426004311404627406132328947657274877275719882979792982905046104421923507813744640000

noncomputable def p18617 :=
nat_lit
  44266314869211223579669798590599987573835947719447874049008212938475563618023196251025499770127540306631740610630768578466810492677895241740985803031189037864376008038827822551537173817897266662108164659807398872554652542395736819580392105755745276942512196603264318693087031184106581063533404741578611241908665780944082802367273422610426598466582120727615868346172440576

noncomputable def p18618 :=
nat_lit
  134380070666626307910579618951129019042203539280705125941534153706062819328273898230096092426845733372208831829667050723202892909539414783111189054483475157760000977710393559207680243954288251664725718422150114649834149959227153855770958331774549753463951360121384981962136837242834551454258898028709682238887832034865891888237959496178449237078204708332159654812984857569018140096987136

noncomputable def p18619 :=
nat_lit
  10146851554696296058247560082762333928932542781986900955160210367198507523105709373862669478565991110785338897525991447922399131313382580923601394735292146421359465691011767089792869431423385736957942404890805277345678734698181532792787983511119095233921259748344819050018279469281602441242678516888872812406995934468930816567986908830496650691292968332179051065650121464330304975011840000

noncomputable def p18620 :=
BSN.cos_dyadic_bound_f 3406462939768322048 2305843009213693952 6 5
  1125899906842624 432960000000001 p18615 p18616
  p18617 p18618 p18619

noncomputable def p18621 :=
@BSN.binarySplit_of_base5 (BSN.cosEvenP 3406462939768322048) (BSN.cosEvenQ 2305843009213693952)
  0 5 p18615 p18616 p18617
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p18622 :=
p18620 p18617 105094243180298 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p18621 (Eq.refl true))

noncomputable def p18623 :=
@BSN.binarySplit_of_base5 (BSN.cosOddP 3406462939768322048) (BSN.cosOddQ 2305843009213693952)
  0 5 p18618 p18619 p18617
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p18624 :=
@BSN.cos_arg_round false 105094243180298 1125899906842624 p18611
  p18612 3406462939768322048 2305843009213693952 432960000000001
  432537600000000
  (p18622 (p18623 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p18625 :=
p18613 105094243180298 1125899906842624 0 1000000000000000
  432537600000000 216268800000000 p18614 BSN.pi_near_15 p18624
  (Eq.refl true) (Eq.refl true)

noncomputable def p18626 :=
@p18513 52547121590149 562949953421312 854667841
  3628388371660800000000
  (@p18514 105094243180298 1125899906842624 14338946976710656
    p18597 52547121590149 562949953421312 854667841
    3628388371660800000000
    (p18610 (p18625 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p18627 :=
@p18512 52547121590149 562949953421312 854667841
  3628388371660800000000 6031018264484142 6031018264514581 562949953421312
  p18626 (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p18628 :=
@Enclosure.Real.IsNear.recentre' p18510 false 12062036528998723
  1125899906842624 30439 1125899906842624 12062036528998723
  1125899906842624 30439 1125899906842624
  (p18627 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p18629 :=
nat_lit
  24144729381954847719531080833021902521225617532176615617847359730477506742604972443724528193149308891093202052332134428109900281398953384678375160325

noncomputable def p18630 :=
@Enclosure.Real.IsNear.subLit_tt_n p18587
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p18588
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
        (Enclosure.sfrac false 12 1))))
  p18629 p18592

noncomputable def p18631 :=
nat_lit
  17470656116015560259047369530649762924940469600921933152843431963410172562221292624896880102203627658167200206350537207811824273655730608179841008193281002095791119603614162794523282103189082031856941

noncomputable def p18632 :=
nat_lit 29825194111497780083659652951386184360947999362400488393368729006734381112547970762319375

noncomputable def p18633 :=
nat_lit 248661618204893321077691124073410420050228075398673858720231988446579748506266687766528

noncomputable def p18634 :=
nat_lit
  8655989682974535745161882306374932093873852036281644091508335610308576265002337977330909934171697414829471600284670299571419

noncomputable def p18635 :=
nat_lit
  4697501107284327477822780708762300448574536044183469349107493049823395840000000000000000000000000000000000000000000000000000000000000

noncomputable def p18636 :=
nat_lit
  45035064486605398116895235021696013017137936031860405896054126653714671542348995586645754614511011477543459103525811808010537666299111145707711384034790022750645963835000169432292575015450994849816833995776870046854199223193803161600

noncomputable def p18637 :=
@p18630 p18631 p18594 p18632
  p18633 p18634 p18635 p18636
  p18591 p18592 p18593 p18594

noncomputable def p18638 :=
@Enclosure.Real.IsNear.subLit_tf p18585
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 3 1) p18586)
    (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
        (Enclosure.sfrac false 12 1))))

noncomputable def p18639 :=
nat_lit
  22095779291204767088678552748131060484087753556481376544261044434274522501790985367983609838589781200310624369345501298350657081883158800342826744325

noncomputable def p18640 :=
nat_lit
  17394432469698689291811829558013460892595637761329556662902146059264346680145167163071667758625334842569040196315308961988578274140071665902566836486636639995459300205358006799738536775184781231856941

noncomputable def p18641 :=
nat_lit
  1616336623341782894032496631905727739210532796600763649705556667204463496888039647613412548885152084665980265688587875

noncomputable def p18642 :=
nat_lit
  157608024785577916849116160400574455220318957081861786671793173616982887085988842445657065019539662563226511961227264

noncomputable def p18643 :=
nat_lit
  37316952208460380265012824707592578497831319609811401842032623855789422519764862683178103787332545898259966493024659811807909184275536288617568086592080880962523

noncomputable def p18644 :=
nat_lit
  6396747175824145469252491254551266195206449368327585882798902855025592523781573287181265709853310976000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p18645 :=
nat_lit
  3805403106872211017057937040999870390735457716306071174817620241312454662889801055677186389724778390238043905514133652775952689793601351276163829481445896555227438545719928449419349539477281745770272480035847616102855482454028522250228172934463266849451399761100800

noncomputable def p18646 :=
@p18638 p18639 p18592 p18640
  p18594 p18641 p18642 p18643
  p18644 p18645 p18629 p18592

noncomputable def p18647 :=
@Enclosure.Real.IsNear.subLit_tf p18583
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 3 1) p18584)
    (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
        (Enclosure.sfrac false 12 1))))

noncomputable def p18648 :=
nat_lit 2900127961551477565172238919047914926783555124644041264869058311287147006074002594474358087718857742425

noncomputable def p18649 :=
nat_lit
  4674811236257191413899155874270980938109600944396907886845192945083693162857577078035146350860879763772555072572220106224094521871

noncomputable def p18650 :=
nat_lit
  51286458754759247472273794340140899135359540550976483361047847617107073129417504351846400000000000000000000000000000000000000000000000000000

noncomputable def p18651 :=
nat_lit
  17956578349528382003806004721397569508756117903362059523312779239547677891108958022172350771758958373221845022717402599481074043720691793493396421125

noncomputable def p18652 :=
nat_lit
  17393241490691432646776694082227526545819020234884763833488842223553630062841174280507803543186323147623774184198432541711655527538782264199944219195132649548646409903794864655738536775184781231856941

noncomputable def p18653 :=
nat_lit
  3093056593237317907857911337828679480184395321757660354311579920607756171422270066151211935896917252811350296718804603367947871500031487597926719071267033265770961085103366679488342519633289921416653627390088539556178186502637651635336828874339123200

noncomputable def p18654 :=
@p18647 p18648 p5240 p18649
  p18650 p18651 p18592 p18652
  p18594 p18653 p18639 p18592

noncomputable def p18655 :=
@Enclosure.Real.IsNear.subLit_tt_n
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p18580
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p18503 (Enclosure.sfrac false 1 16)))))

noncomputable def p18656 :=
@p18655
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p18582
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 4 1) Real.pi))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p18503 (Enclosure.sfrac false 1 16)))))

noncomputable def p18657 :=
nat_lit 3606979008690108964006095511629114143505891800183559926456377710496682028230302255933287683494518593625

noncomputable def p18658 :=
nat_lit
  1371003824216665912583194797436752856699010655208260023384234952330668823917253426806216715038619988376951135341372106224094521871

noncomputable def p18659 :=
nat_lit 1981018573723506121917991984761863638173522968013642717075

noncomputable def p18660 :=
nat_lit 404542390526920756404507735424469327600503409245775682852647267666117665967

noncomputable def p18661 :=
nat_lit 6279889847906223476656458265577778600084085145600000000000000000000000000000000000000

noncomputable def p18662 :=
nat_lit
  1137774891268638550721905798592619356605473144597444287413052538834359632393802221135170577959799194055460491668987634323520724356103406662227918999981444300800

noncomputable def p18663 :=
@p18656 p18657 p5240 p18658
  p18650 p18659 p1053 p18660
  p18661 p18662 p18648 p5240

noncomputable def p18664 :=
nat_lit 12827751466941012993089344537792822208679745585851683004699772045283374514741756543662875

noncomputable def p18665 :=
@Enclosure.Real.IsNear.mulLit_ft p18580
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p18503 (Enclosure.sfrac false 1 16))))
  p18664

noncomputable def p18666 :=
nat_lit 497323236409786642155382248146820840100456150797347717440463976893159497012533375533056

noncomputable def p18667 :=
nat_lit 169747604531548856332897003269995152158694341455358229267543647169498401611541780040433694337669085275538081

noncomputable def p18668 :=
nat_lit
  14134776518227074636666380005943348126619871175004951664972849610340958208000000000000000000000000000000000000000000000

noncomputable def p18669 :=
@p18665 p18666 p18667 p18668
  281185601232283 281474976710656 4145663807 7256776743321600000000
  p18657 p5240 p18658 p18650

noncomputable def p18670 :=
@Enclosure.Real.IsNear.mulLit_ff p18579
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p18671 :=
nat_lit 54798292310257640149021973282127708063589432423561984329225

noncomputable def p18672 :=
nat_lit 6277101735386680763835789423207666416102355444464034512896

noncomputable def p18673 :=
nat_lit 15840862264424599039535702184425358763948353201635775647388535448371

noncomputable def p18674 :=
nat_lit 5846006549323611672814739330865132078623730171904000000000000000000000000000000

noncomputable def p18675 :=
nat_lit 234090350741455467086246322435

noncomputable def p18676 :=
nat_lit 1108703056397918788798348511

noncomputable def p18677 :=
nat_lit 2417851639229258349412352000000000000000

noncomputable def p18678 :=
@p18670 p18671 p18672 p18673
  p18674 p18675 p2316 p18676
  p18677 p18664 p18666 p18667

noncomputable def p18679 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p18680 :=
@p18679
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p18681 :=
@p18680 p18675 p2316 p18676
  p18677 p18675 p2316 p18676
  p18677 p18671 p18672 p18673

noncomputable def p18682 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
        (Enclosure.sfrac false 12 1)))
    (Enclosure.sfrac false 1 1))
  884279719003555

noncomputable def p18683 :=
@p18682 140737488355328 1 500000000000000 264724323888417
  562949953421312 41 562949953421312 p18675 p2316
  p18676 p18677

noncomputable def p18684 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 2 1)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
      (Enclosure.sfrac false 12 1)))
  (Enclosure.sfrac false 1 1) 827674277309729 562949953421312

noncomputable def p18685 :=
@p18684 41 562949953421312 1 1 0 1
  264724323888417 264724323888417 562949953421312 41 562949953421312

noncomputable def p18686 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 2 1)
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
    (Enclosure.sfrac false 12 1))
  2 1 0 1

noncomputable def p18687 :=
@p18686 827674277309729 1125899906842624 41 1125899906842624
  827674277309729 562949953421312 41 562949953421312
  (Enclosure.Real.IsNear.const false 2 1)
  (@p18603 1 827674277309729 827674277309729 1125899906842624
    41 1125899906842624 (p18608 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p18688 :=
@p18681 p18674
  (p18683 d238
    (p18685 (p18687 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (p18683 d238
    (p18685 (p18687 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))

noncomputable def p18689 :=
@p18678 p18668 (p18688 (Eq.refl true))
  (p18683 d238
    (p18685 (p18687 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p18690 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p18503 (Enclosure.sfrac false 1 16))))
  true

noncomputable def p18691 :=
nat_lit 121748510886483040665600000000

noncomputable def p18692 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p18503 (Enclosure.sfrac false 1 16)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Neg.neg.{0} Real Real.instNeg (@Nat.cast.{0} Real Real.instNatCast 1819617339640199))
    (@Nat.cast.{0} Real Real.instNatCast 1125899906842624))
  true

noncomputable def p18693 :=
nat_lit 288329876597574096589664969666858636093487005

noncomputable def p18694 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p18503 (Enclosure.sfrac false 1 16)))
  true p18693

noncomputable def p18695 :=
nat_lit 178405961588244985132285746181186892047843328

noncomputable def p18696 :=
nat_lit 3080055059125238643467131477243061252396853

noncomputable def p18697 :=
nat_lit 5444517870735015415413993718908291383296000000000000000

noncomputable def p18698 :=
nat_lit 326061844913142180445052985791

noncomputable def p18699 :=
nat_lit 246833682398877842851509035455

noncomputable def p18700 :=
@p18544 (Enclosure.sfrac false 1 16) p18699
  p14431 114031186919947043 p14431 1 16 0

noncomputable def p18701 :=
nat_lit 5216989518610274887120847772656

noncomputable def p18702 :=
nat_lit 685044709320182181377798053441

noncomputable def p18703 :=
@Enclosure.Real.IsNear.subLit_ff_n
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
      (Enclosure.sfrac false 12 1))
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
      (Enclosure.sfrac false 12 1)))
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
    (Enclosure.sfrac false 12 1))
  p18702

noncomputable def p18704 :=
nat_lit 277910020018518402569668838431845116721233920

noncomputable def p18705 :=
@p18703 p14431 67869290739399459 p14431
  827674277309729 1125899906842624 41 1125899906842624 p18704
  p18699 p14431 114031186919947043

noncomputable def p18706 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
    (Enclosure.sfrac false 12 1))
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
    (Enclosure.sfrac false 12 1))
  827674277309729 1125899906842624 41

noncomputable def p18707 :=
@p18706 1125899906842624 827674277309729 1125899906842624 41
  1125899906842624 p18702 p14431 67869290739399459
  p14431
  (@p18603 1 827674277309729 827674277309729 1125899906842624
    41 1125899906842624 (p18608 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p18708 :=
p18707
  (@p18603 1 827674277309729 827674277309729 1125899906842624
    41 1125899906842624 (p18608 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p18709 :=
@p18705 p14431 (p18708 (Eq.refl true))
  (@p18603 1 827674277309729 827674277309729 1125899906842624
    41 1125899906842624 (p18608 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p18710 :=
@p18543 500000000000000 p18698 p14431
  114031186919947043 p14431 p18693 p18695
  p18696 p18697 d238
  (@p18700 1 p18701 p18698 p14431
    114031186919947043 p14431
    (p18709 (Eq.refl true) (Eq.refl true))
    (Enclosure.Real.IsNear.const false 1 16) (Eq.refl true)
    (Eq.refl true))

noncomputable def p18711 :=
@p18692 1819617339640199 1125899906842624 319 562949953421312
  true 562371202464566 562949953421312 1 216268800000000
  (@p18694 p18695 p18696 p18697
    1819617339640199 1125899906842624 319 562949953421312
    (p18710 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_true_div 1819617339640199 1125899906842624)

noncomputable def p18712 :=
nat_lit
  135140022951538365678963214353952790614237836691669104778331281797247825457326290864799005415293964133564529643649012829475331376068810708381077143413432608887294208157936132683685150346246690695467649458571132872274665454033932703659672201838882299585921

noncomputable def p18713 :=
nat_lit
  2371728904138043385318735560374504222700605579872037175997883585289299297944925459400262945270439995320386160994569494400873352117161187529222914467416668525224467727137180455887633346091077280717708110065332645507572399051088361938793378954328561156096000

noncomputable def p18714 :=
nat_lit
  14443786724399843620780154662952570842912859148801264958227043636803263360045347960233354635371007032260690632220117905801732945744406374692468941458156644935657607751580574390191646341176911009266903009418956986746919283778091257019316810556801

noncomputable def p18715 :=
nat_lit
  1098893894221825860921747719607926923423664656632188403019617864452418272599181990826621852036611756778864462543929541606145075836790027532958332076088336882529910734532602528922536250058432040757899577028776371963880114831080470775307132774793089536763265

noncomputable def p18716 :=
nat_lit
  135188547535868472963167926941346740693934518052706119031879364361490059982860751185814987880415079733262011176690461180849781070678187689165706124642750105937794660446819285985595100727191405000909362273723960793931626745912036630511222600396727985897472000

noncomputable def p18717 :=
BSN.sin_dyadic_bound_f 1819617339640199 1125899906842624 5 4
  562949953421312 216268800000000 p18712 p18713
  p18714 p18715 p18716

noncomputable def p18718 :=
@BSN.binarySplit_of_base4 (BSN.sinEvenP 1819617339640199) (BSN.sinEvenQ 1125899906842624)
  0 4 p18712 p18713 p18714
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p18719 :=
p18717 p18714 562371202464566 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p18718 (Eq.refl true))

noncomputable def p18720 :=
@BSN.binarySplit_of_base4 (BSN.sinOddP 1819617339640199) (BSN.sinOddQ 1125899906842624) 0
  4 p18715 p18716 p18714 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p18721 :=
p18711
  (BSN.sin_neg_of_bound 1819617339640199 1125899906842624 false 562371202464566
    562949953421312 1 216268800000000
    (p18719 (p18720 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p18722 :=
p18669 p18689
  (@p18690 562371202464566 562949953421312 69552697153421312
    p18691 281185601232283 281474976710656 4145663807
    7256776743321600000000 (p18721 (Eq.refl true))
    (Eq.refl true))

noncomputable def p18723 :=
nat_lit 621004048725293619848776562859290404323769275

noncomputable def p18724 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p18582
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 4 1) Real.pi))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p18503 (Enclosure.sfrac false 1 16))))
  p18723

noncomputable def p18725 :=
nat_lit 5575186299632655785383929568162090376495104

noncomputable def p18726 :=
nat_lit 89942729001289853333700916775679977839207374173574411

noncomputable def p18727 :=
nat_lit 5192296858534827628530496329220096000000000000000000000000000000

noncomputable def p18728 :=
@p18724 p18725 p18726 p18727
  3190025214473 70368744177664 4145663807 7256776743321600000000
  p18659 p1053 p18660 p18661

noncomputable def p18729 :=
nat_lit 702271052224366401258738967305

noncomputable def p18730 :=
nat_lit 3326109169193756366395045533

noncomputable def p18731 :=
@Enclosure.Real.IsNear.mulLit_ff p18582
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 4 1) Real.pi)
  p18729 p2316 p18730 p18677

noncomputable def p18732 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 3 1)
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p18733 :=
@p18732 3 1 0 1 p18675
  p2316 p18676 p18677 p18729
  p2316 p18730

noncomputable def p18734 :=
@p18733 p18677 (Enclosure.Real.IsNear.const false 3 1)
  (p18683 d238
    (p18685 (p18687 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p18735 :=
@p18731 884279719003555 70368744177664 1 250000000000000
  p18723 p18725 p18726 p18727
  p18734 d240 (Eq.refl true)

noncomputable def p18736 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p18503 (Enclosure.sfrac false 1 16)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Neg.neg.{0} Real Real.instNeg (@Nat.cast.{0} Real Real.instNatCast 1819617339640199))
    (@Nat.cast.{0} Real Real.instNatCast 1125899906842624))
  true

noncomputable def p18737 :=
@p18736 1819617339640199 1125899906842624 319 562949953421312
  true 25520201715784 562949953421312 1 216268800000000
  (@p18694 p18695 p18696 p18697
    1819617339640199 1125899906842624 319 562949953421312
    (p18710 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_true_div 1819617339640199 1125899906842624)

noncomputable def p18738 :=
nat_lit
  7440312811089865443030347252996350188864065637480798725684111517059493393500796666802358533274144694716264654442128004435495111284504945246339768277649714815483504709298672211152057461606184443547950573410743755168406441154682334851085796686465162190411911719391349878173642196730270239676414142799568148993903042963681

noncomputable def p18739 :=
nat_lit
  26068754422020242755335860258679067180644360935168211642010495233358709885485065609561450188402496767899127163308765923818732185965496218501019777765128248418025372493348965463231703293438828334554344859193466359040392401283092440636892428972474131770237648762755971780096283208066310154669126010645890362914782576640000

noncomputable def p18740 :=
nat_lit
  158343898699397410231945319056356816511033188248071746811967031542721187794115239170426284863901277967686364175526380933667946138376322946063158605428390521898380210823364753147315191245868083474471587687227522637697550947068813649520162629125769340775369540354062853167331627890621998882884641000734796001

noncomputable def p18741 :=
nat_lit
  114271656893094331290251909582199422906252025483336832071290789611448959428075849516130523097885879551858018270841953667998245705868985301884174533517985677493348098069436890361307660493079458796284558635046734308450200508104617421648849393192998589357226848613243632758891793427696899801898071530146933322767998662158561

noncomputable def p18742 :=
nat_lit
  6021882271486676076482583719754864518728847376023856889304424398905861983547050155808694993520976753384698374724324928402127134958029626473735568663744625384563861045963611022006523460784369345282053662473690728938330644696394353787122151092641524438924896864196629481202241421063317645728568108459200673833314775203840000

noncomputable def p18743 :=
BSN.cos_dyadic_bound_t 1819617339640199 1125899906842624 6 5
  562949953421312 216268800000000 p18738 p18739
  p18740 p18741 p18742

noncomputable def p18744 :=
@BSN.binarySplit_of_base5 (BSN.cosEvenP 1819617339640199) (BSN.cosEvenQ 1125899906842624)
  0 5 p18738 p18739 p18740
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p18745 :=
p18743 p18740 25520201715784 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p18744 (Eq.refl true))

noncomputable def p18746 :=
@BSN.binarySplit_of_base5 (BSN.cosOddP 1819617339640199) (BSN.cosOddQ 1125899906842624) 0
  5 p18741 p18742 p18740 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p18747 :=
p18737
  (BSN.cos_neg_of_bound 1819617339640199 1125899906842624 true 25520201715784
    562949953421312 1 216268800000000
    (p18745 (p18746 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p18748 :=
p18728 p18735
  (@p18538 25520201715784 562949953421312 69552697153421312
    p18691 3190025214473 70368744177664 4145663807
    7256776743321600000000 (p18747 (Eq.refl true))
    (Eq.refl true))

noncomputable def p18749 :=
nat_lit 2973791044762212974892913502175

noncomputable def p18750 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 3 1) p18584)
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
      (Enclosure.sfrac false 12 1)))
  p18749

noncomputable def p18751 :=
nat_lit 23095162349864473631121971316090247

noncomputable def p18752 :=
nat_lit 5194603131156609735065600000000000000000000000

noncomputable def p18753 :=
nat_lit
  6038278439621909033871597621403771795514582233335802703825387383787474871258192711830173088588667179217105458127137435

noncomputable def p18754 :=
nat_lit
  1260864198284623334792929283204595641762551656654894293374345388935863096687910739565256520156317300505812095689818112

noncomputable def p18755 :=
nat_lit
  5575327189983547478946401703856433741363494681462901271541693996905801208305087407260696808144358274013216885845455665021436929055935627787225156704929

noncomputable def p18756 :=
nat_lit
  78603229296527099526174612535925959006696849838009375327832918282554480932227972552883393042677485273088000000000000000000000000000000000000000000000000000000

noncomputable def p18757 :=
@p18750 p3344 p18751 p18752
  p18753 p18754 p18755 p18756
  p18651 p18592 p18652 p18594

noncomputable def p18758 :=
nat_lit 991263681587404324964304500725

noncomputable def p18759 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 3 1) p18584
  3 1 0 1 p18758 p3344

noncomputable def p18760 :=
nat_lit 15583809393469829205196800000000000000000000000

noncomputable def p18761 :=
@Enclosure.Real.IsNear.neg
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
          (Enclosure.sfrac false 12 1)))))

noncomputable def p18762 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
        (Enclosure.sfrac false 12 1))))
  884279719003555

noncomputable def p18763 :=
@p18762 140737488355328 1 500000000000000 1120984299746695
  1125899906842624 854667841 3628388371660800000000 p18758
  p3344 p18751 p18760

noncomputable def p18764 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
        (Enclosure.sfrac false 12 1))))
  true

noncomputable def p18765 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
      (Enclosure.sfrac false 12 1)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 5200430858322971)
    (@Nat.cast.{0} Real Real.instNatCast 1125899906842624))
  false

noncomputable def p18766 :=
@p18765 5200430858322971 1125899906842624 65 281474976710656
  true 1120984299746695 1125899906842624 1 216268800000000
  (@p18600 p3344 p18601 p18602
    5200430858322971 1125899906842624 65 281474976710656
    (p18609 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div 5200430858322971 1125899906842624)

noncomputable def p18767 :=
BSN.sin_reduce2
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 5200430858322971)
    (@Nat.cast.{0} Real Real.instNatCast 1125899906842624))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast p18611)
    (@Nat.cast.{0} Real Real.instNatCast p18612))
  226375608064910080 72057594037927936 false

noncomputable def p18768 :=
nat_lit
  9031138170066165468517994579249020730260441321344488319684437731152963010214025021838508024413597835369320916923779970725349992553428474763391717059434326914021629923261617418971728226578721778603121715883490653679906554240450644550488294210700649299526204097662073290519605803822059926839387030624147603456

noncomputable def p18769 :=
nat_lit
  227166498108393291591690474249109426965528421018278839661455426590473243066834650624926416047854179247596172938820614485527445924608820872880385787908168637421617142754592441181269508473347051925777211342581761153821293384735107078859788885002196634811247029175151612501537270086431278076342027182518829056000

noncomputable def p18770 :=
nat_lit
  328744650948866984485401470521172953057178707674270535728066337630267453032444666660075043427952416093799767631788345777451985984079866219769017400357688643250746866753256635081450484442770761622553625886758517970487240114967185881586852398861600735369771646322815731793997126178157700447140315136

noncomputable def p18771 :=
nat_lit
  73467748904513181282588785982999853985309694887365534383804055161791978837947170861951578613091191177557940639203126466229517666967823728394459202398345154598155182169665270658839500070683448109165040721510513523290901713090691543644967750478909587840418788933470531690869283225871407714392925477371998371840

noncomputable def p18772 :=
nat_lit
  12948490392178417620726357032199237337035119998041893860702959315656974854809575085620805714727688217112981857512775025675064417702702789754181989910765612333032177137011769147332361982980781959769301046527160385767813722929901103495007966445125208184241080662983641912587624394926582850351495549403573256192000

noncomputable def p18773 :=
BSN.sin_dyadic_bound_f 3406462939768322048 2305843009213693952 5 4
  1125899906842624 432960000000001 p18768 p18769
  p18770 p18771 p18772

noncomputable def p18774 :=
@BSN.binarySplit_of_base4 (BSN.sinEvenP 3406462939768322048) (BSN.sinEvenQ 2305843009213693952)
  0 4 p18768 p18769 p18770
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p18775 :=
p18773 p18770 1120984299746695 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p18774 (Eq.refl true))

noncomputable def p18776 :=
@BSN.binarySplit_of_base4 (BSN.sinOddP 3406462939768322048) (BSN.sinOddQ 2305843009213693952)
  0 4 p18771 p18772 p18770
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p18777 :=
@BSN.sin_arg_round false 1120984299746695 1125899906842624 p18611
  p18612 3406462939768322048 2305843009213693952 432960000000001
  432537600000000
  (p18775 (p18776 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p18778 :=
p18767 1120984299746695 1125899906842624 0 1000000000000000
  432537600000000 216268800000000 p18614 BSN.pi_near_15 p18777
  (Eq.refl true) (Eq.refl true)

noncomputable def p18779 :=
p18763 d238
  (@p18764 1120984299746695 1125899906842624 14338946976710656
    p18597 1120984299746695 1125899906842624 854667841
    3628388371660800000000
    (p18766 (p18778 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p18780 :=
@Neg.neg.{0} Real Real.instNeg
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p18579
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p18503 (Enclosure.sfrac false 1 16)))))

noncomputable def p18781 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18780
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 4 1) Real.pi)
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p18503 (Enclosure.sfrac false 1 16)))))

noncomputable def p18782 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18781
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) p18584)
    (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
        (Enclosure.sfrac false 12 1))))

noncomputable def p18783 :=
@Enclosure.Real.IsNear.of_eq
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
      (Enclosure.sfrac false 12 1)))
  (p18502
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18782
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p18586
        (Zeta.RiemannSiegel.correction
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
            (Enclosure.sfrac false 12 1))))))

noncomputable def p18784 :=
@p18506
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18782
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p18586
      (Zeta.RiemannSiegel.correction
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
          (Enclosure.sfrac false 12 1)))))
  12062036528998723

noncomputable def p18785 :=
nat_lit 500601902929500596151082887643695406384729182937940015170053472583613581721286294935082365077398886345

noncomputable def p18786 :=
nat_lit
  29577106926476413167619352231061178860504084373765252757333329422280636383192606931833812693471290407150466793839631466592272809455799813

noncomputable def p18787 :=
@p18784 1125899906842624 30439 1125899906842624 p18785
  p2734 p18786 p8047 p18753
  p18754 p18755 p18756

noncomputable def p18788 :=
nat_lit 1503605131354837827138279905714515830354923185949432198927512388779618930834327013053660486481133824055

noncomputable def p18789 :=
@Enclosure.Real.IsNear.subLit_ff_n p18782
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p18586
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
        (Enclosure.sfrac false 12 1))))
  p18788 p2734

noncomputable def p18790 :=
nat_lit
  29435973786639836697876159336701987722251514005391695582015583525884152898799036291061126937677452162537581288811994842144348995055799813

noncomputable def p18791 :=
nat_lit 1581040575315862650988387614959481225360630466035558615957111604496419775

noncomputable def p18792 :=
nat_lit 883423532389192164791648750371459257913741948437809479060803100646309888

noncomputable def p18793 :=
nat_lit 17273703400442624940532825989585506883003661061150127336941643800552908860433472520247348875782041

noncomputable def p18794 :=
nat_lit 546861103186887628145373974549851898170837206321706686763499520000000000000000000000000000000000000000000000

noncomputable def p18795 :=
nat_lit
  442243501406730901947846397569996269865650433973578535034648582419900166089140977908437403748228345616555982215811419576393902156263431280665400213350307125272455064961679360

noncomputable def p18796 :=
@p18789 p18790 p8047 p18791
  p18792 p18793 p18794 p18795
  p18785 p2734 p18786 p8047

noncomputable def p18797 :=
@Enclosure.Real.IsNear.subLit_ff_p p18781
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) p18584)
    (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
        (Enclosure.sfrac false 12 1))))

noncomputable def p18798 :=
nat_lit 5719815180488778859575406406210727217347878803977980352514516221066256465

noncomputable def p18799 :=
nat_lit 441711766194596082395824375185729628956870974218904739530401550323154944

noncomputable def p18800 :=
nat_lit 43458953576886454230562200086084598745859361435533608429476388658870864296335253327045231

noncomputable def p18801 :=
nat_lit 3535263697369778606192316603150557725548846586322144237663027200000000000000000000000000000000000000

noncomputable def p18802 :=
nat_lit 12997849162127439792707302287738105441404148973095418384429258221217904167898822832732106848795631687625

noncomputable def p18803 :=
nat_lit
  29381047779262569286099613842671521502193993833334885444066602639693359359570388338292611934815672817255149205425938793504348995055799813

noncomputable def p18804 :=
nat_lit
  664160078230003057300762697906560430429952673143390894009982866641202572382533973934919622491429058683328808789379993818414201161883923041256682133222046185022843218999377920

noncomputable def p18805 :=
@p18797 p18798 p18799 p18800
  p18801 p18802 p2734 p18803
  p8047 p18804 p18788 p2734

noncomputable def p18806 :=
@Enclosure.Real.IsNear.subLit_ft p18780
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 4 1) Real.pi)
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p18503 (Enclosure.sfrac false 1 16)))))

noncomputable def p18807 :=
nat_lit 174807934179783775174270676000509117653327810689189659238445445666873425

noncomputable def p18808 :=
nat_lit 54196168111836854158677682315485838863399180083469904690181211265111514361005759981135693

noncomputable def p18809 :=
nat_lit 10605791092109335818576949809451673176646539758966432712989081600000000000000000000000000000000000000

noncomputable def p18810 :=
nat_lit 248646724445528879780857766065

noncomputable def p18811 :=
nat_lit 111937467268943742902803317161477369

noncomputable def p18812 :=
nat_lit 113292611667830293905043610886348603685617751242537895182474770390605649208852733170201307306849730560

noncomputable def p18813 :=
@p18806 p18807 p18799 p18808
  p18809 p18810 p1070 p18811
  p18760 p18812 p18798 p18799

noncomputable def p18814 :=
@Enclosure.Real.IsNear.neg
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p18579
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p18503 (Enclosure.sfrac false 1 16)))))

noncomputable def p18815 :=
@Enclosure.Real.IsNear.mulLit_ft p18579
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p18503 (Enclosure.sfrac false 1 16))))
  p18671

noncomputable def p18816 :=
@p18815 p18672 p18673 p18674
  3190025214473 70368744177664 4145663807 7256776743321600000000
  p18807 p18799 p18808 p18809

noncomputable def p18817 :=
p18816 (p18688 (Eq.refl true))
  (@p18538 25520201715784 562949953421312 69552697153421312
    p18691 3190025214473 70368744177664 4145663807
    7256776743321600000000 (p18747 (Eq.refl true))
    (Eq.refl true))

noncomputable def p18818 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 4 1) Real.pi)
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p18503 (Enclosure.sfrac false 1 16))))
  884279719003555

noncomputable def p18819 :=
@p18818 70368744177664 1 250000000000000 281185601232283
  281474976710656 4145663807 7256776743321600000000 p18810
  p1070 p18811 p18760

noncomputable def p18820 :=
p18819 d240
  (@p18690 562371202464566 562949953421312 69552697153421312
    p18691 281185601232283 281474976710656 4145663807
    7256776743321600000000 (p18721 (Eq.refl true))
    (Eq.refl true))

noncomputable def p18821 :=
@p18805 p18790 p8047
  (@p18813 p18800 p18801
    (@p18814 true p18807 p18799 p18808
      p18809 (p18817 (Eq.refl true)))
    (p18820 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p18822 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 2 1) p18584)
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
      (Enclosure.sfrac false 12 1)))
  p18758

noncomputable def p18823 :=
nat_lit 7791904696734914602598400000000000000000000000

noncomputable def p18824 :=
nat_lit 13112403292444603736116461238986018465422935782359117801211860135112867845

noncomputable def p18825 :=
nat_lit 14134776518227074636666380005943348126619871175004951664972849610340958208

noncomputable def p18826 :=
nat_lit 75313427099871093479706515697450980063155352859297591668365222018315675360956231910206401

noncomputable def p18827 :=
nat_lit 143356357033823470392540915184396375994095948613997477694930818170880000000000000000000000000000000

noncomputable def p18828 :=
@p18822 p2316 p18751 p18823
  p18824 p18825 p18826 p18827
  p18802 p2734 p18803 p8047

noncomputable def p18829 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 2 1) p18584
  2 1 0 1 p18758 p3344

noncomputable def p18830 :=
@Neg.neg.{0} Real Real.instNeg
  (p18578
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p18503 (Enclosure.sfrac false 1 16)))))

noncomputable def p18831 :=
@Enclosure.Real.IsNear.of_eq
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
      (Enclosure.sfrac false 12 1)))
  (p18502
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18830
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p18584
        (Zeta.RiemannSiegel.correction
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
            (Enclosure.sfrac false 12 1))))))

noncomputable def p18832 :=
@p18506
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18830
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p18584
      (Zeta.RiemannSiegel.correction
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
          (Enclosure.sfrac false 12 1)))))
  12062036528998723

noncomputable def p18833 :=
nat_lit 1087080383227215472625753842396157574518291833601342069015

noncomputable def p18834 :=
nat_lit 12554203470773361527671578846415332832204710888928069025792

noncomputable def p18835 :=
nat_lit 12432034738058935087458022903505030501857022607811762804566797609150832971

noncomputable def p18836 :=
nat_lit 254652045288536524467810045252485153344849686288138240000000000000000000000000000000

noncomputable def p18837 :=
@p18832 1125899906842624 30439 1125899906842624 p18833
  p18834 p18835 p18836 p18824
  p18825 p18826 p18827

noncomputable def p18838 :=
nat_lit 65822836015912160068659391269119812949169105

noncomputable def p18839 :=
@Enclosure.Real.IsNear.subLit_ff_n p18830
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p18584
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
        (Enclosure.sfrac false 12 1))))
  p18838 p2325

noncomputable def p18840 :=
nat_lit 9413356192538849466883956820748016805295044053313

noncomputable def p18841 :=
nat_lit 4386452386090222380582563298925137100800000000000000000000000

noncomputable def p18842 :=
nat_lit 38142042852443623922942018913202792079997237515643741034775

noncomputable def p18843 :=
nat_lit 11885549743701988781163767379303668032020296230661161871229961922750832971

noncomputable def p18844 :=
nat_lit 24242702636671155202119958067847039595692889202808425389727846454313301154050521862298472653510410240

noncomputable def p18845 :=
@p18839 p18840 p18841 p18842
  p18834 p18843 p18836 p18844
  p18833 p18834 p18835 p18836

noncomputable def p18846 :=
@Enclosure.Real.IsNear.neg
  (p18578
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p18503 (Enclosure.sfrac false 1 16)))))

noncomputable def p18847 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p18848 :=
@p18847
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p18503 (Enclosure.sfrac false 1 16))))
  p18675

noncomputable def p18849 :=
@p18848 p2316 p18676 p18677
  281185601232283 281474976710656 4145663807 7256776743321600000000
  p18838 p2325 p18840 p18841

noncomputable def p18850 :=
p18849
  (p18683 d238
    (p18685 (p18687 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (@p18690 562371202464566 562949953421312 69552697153421312
    p18691 281185601232283 281474976710656 4145663807
    7256776743321600000000 (p18721 (Eq.refl true))
    (Eq.refl true))

noncomputable def p18851 :=
@Enclosure.Real.IsNear.mulLit_ff p18584
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
      (Enclosure.sfrac false 12 1)))
  p18758 p3344 p18751

noncomputable def p18852 :=
nat_lit 38478200665400311822018117979

noncomputable def p18853 :=
nat_lit 30009353603570207673907367

noncomputable def p18854 :=
nat_lit 4085202129641754907167109939200000000

noncomputable def p18855 :=
@p18506
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p18503 (Enclosure.sfrac false 1 16))))
  12062036528998723

noncomputable def p18856 :=
@p18855 1125899906842624 30439 1125899906842624 3190025214473
  70368744177664 4145663807 7256776743321600000000 p18852
  p2316 p18853 p18854

noncomputable def p18857 :=
p18856
  (p18596
    (@Enclosure.Real.IsNear.neg p18510 false 12062036528998723
      1125899906842624 30439 1125899906842624
      (p18628 (Eq.refl true))))
  (@p18538 25520201715784 562949953421312 69552697153421312
    p18691 3190025214473 70368744177664 4145663807
    7256776743321600000000 (p18747 (Eq.refl true))
    (Eq.refl true))

noncomputable def p18858 :=
@p18851 p18760 p18852 p2316
  p18853 p18854 p18842 p18834
  p18843 p18836
  (@p18761 true p18758 p3344 p18751
    p18760 (p18779 (Eq.refl true)))
  (@p18504 false p18852 p2316 p18853
    p18854
    (BSN.correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
        (Enclosure.sfrac false 12 1))
      (p18505 (Eq.refl true) (Eq.refl true)
        (p18286 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p18857 (Eq.refl true)))

noncomputable def p18859 :=
p18837
  (p18596
    (@Enclosure.Real.IsNear.neg p18510 false 12062036528998723
      1125899906842624 30439 1125899906842624
      (p18628 (Eq.refl true))))
  (p18845
    (@p18846 true p18838 p2325 p18840
      p18841 (p18850 (Eq.refl true)))
    (p18858 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p18860 :=
p18828
  (@p18829 p18751 p18760 p18758
    p2316 p18751 p18823
    (Enclosure.Real.IsNear.const false 2 1)
    (@p18761 true p18758 p3344 p18751
      p18760 (p18779 (Eq.refl true)))
    (Eq.refl true))
  (@p18831 false p18824 p18825 p18826
    p18827
    (BSN.deriv_correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
        (Enclosure.sfrac false 12 1))
      (p18505 (Eq.refl true) (Eq.refl true)
        (p18286 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p18859 (Eq.refl true)))

noncomputable def p18861 :=
nat_lit 41089254382353123910068415280239945752815725

noncomputable def p18862 :=
nat_lit 11150372599265311570767859136324180752990208

noncomputable def p18863 :=
nat_lit 622567392302499329690235608706251093507474491827789605764849

noncomputable def p18864 :=
@Enclosure.Real.IsNear.mulLit_ff p18586
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
      (Enclosure.sfrac false 12 1)))
  p18861 p18862 p18863

noncomputable def p18865 :=
nat_lit 66931951692050512399025929243852800000000000000000000000000000000000000

noncomputable def p18866 :=
@Enclosure.Real.IsNear.neg
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 4 1)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
          (Enclosure.sfrac false 12 1)))))

noncomputable def p18867 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 4 1)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
        (Enclosure.sfrac false 12 1))))
  p1068

noncomputable def p18868 :=
@p18867 p1070 p1071 p1072
  52547121590149 562949953421312 854667841 3628388371660800000000
  p18861 p18862 p18863 p18865

noncomputable def p18869 :=
p18868 d242
  (@p18514 105094243180298 1125899906842624 14338946976710656
    p18597 52547121590149 562949953421312 854667841
    3628388371660800000000
    (p18610 (p18625 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p18870 :=
@p18864 p18865 p18852 p2316
  p18853 p18854 p18791 p18792
  p18793 p18794
  (@p18866 true p18861 p18862 p18863
    p18865 (p18869 (Eq.refl true)))
  (@p18504 false p18852 p2316 p18853
    p18854
    (BSN.correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
        (Enclosure.sfrac false 12 1))
      (p18505 (Eq.refl true) (Eq.refl true)
        (p18286 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p18857 (Eq.refl true)))

noncomputable def p18871 :=
p18787
  (p18596
    (@Enclosure.Real.IsNear.neg p18510 false 12062036528998723
      1125899906842624 30439 1125899906842624
      (p18628 (Eq.refl true))))
  (p18796
    (p18821 (p18860 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true))
    (p18870 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p18872 :=
p18757
  (@p18759 p18751 p18760 p18749
    p3344 p18751 p18752
    (Enclosure.Real.IsNear.const false 3 1)
    (@p18761 true p18758 p3344 p18751
      p18760 (p18779 (Eq.refl true)))
    (Eq.refl true))
  (@p18783 false p18753 p18754 p18755
    p18756
    (BSN.iteratedDeriv_two_correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
        (Enclosure.sfrac false 12 1))
      (p18505 (Eq.refl true) (Eq.refl true)
        (p18286 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p18871 (Eq.refl true)))

noncomputable def p18873 :=
@p18654 p18640 p18594
  (@p18663 p18649 p18650
    (p18722 (Eq.refl true)) (p18748 (Eq.refl true))
    (Eq.refl true) (Eq.refl true))
  (p18872 (Eq.refl true)) (Eq.refl true) (Eq.refl true)

noncomputable def p18874 :=
nat_lit 123267763147059371730205245840719837258447175

noncomputable def p18875 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 3 1) p18586)
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
      (Enclosure.sfrac false 12 1)))
  p18874

noncomputable def p18876 :=
nat_lit 22310650564016837466341976414617600000000000000000000000000000000000000

noncomputable def p18877 :=
@p18875 p18862 p18863 p18876
  p18824 p18825 p18826 p18827
  p18641 p18642 p18643 p18644

noncomputable def p18878 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 3 1) p18586
  3 1 0 1 p18861 p18862

noncomputable def p18879 :=
p18877
  (@p18878 p18863 p18865 p18874
    p18862 p18863 p18876
    (Enclosure.Real.IsNear.const false 3 1)
    (@p18866 true p18861 p18862 p18863
      p18865 (p18869 (Eq.refl true)))
    (Eq.refl true))
  (@p18831 false p18824 p18825 p18826
    p18827
    (BSN.deriv_correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
        (Enclosure.sfrac false 12 1))
      (p18505 (Eq.refl true) (Eq.refl true)
        (p18286 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p18859 (Eq.refl true)))

noncomputable def p18880 :=
nat_lit 775119251829170496989989572909264817791442991015903025068125

noncomputable def p18881 :=
nat_lit 3138550867693340381917894711603833208051177722232017256448

noncomputable def p18882 :=
nat_lit 16864209268569162755488613139145098496915581444756701353647316276176172240059764240983

noncomputable def p18883 :=
@Enclosure.Real.IsNear.mulLit_tf p18588
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
      (Enclosure.sfrac false 12 1)))
  p18880 p18881 p18882

noncomputable def p18884 :=
nat_lit 287470543574808813933858868358357785038028800000000000000000000000000000000000000000000000000000

noncomputable def p18885 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 8 1)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi) Real.pi))
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
        (Enclosure.sfrac false 12 1))))

noncomputable def p18886 :=
@p18885 p1059 p1061 p1062
  p1063 1120984299746695 1125899906842624 854667841
  3628388371660800000000 p18880 p18881 p18882

noncomputable def p18887 :=
@p18886 p18884 d243
  (@p18764 1120984299746695 1125899906842624 14338946976710656
    p18597 1120984299746695 1125899906842624 854667841
    3628388371660800000000
    (p18766 (p18778 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p18888 :=
@p18883 p18884 p18852 p2316
  p18853 p18854 p18632 p18633
  p18634 p18635 (p18887 (Eq.refl true))
  (@p18504 false p18852 p2316 p18853
    p18854
    (BSN.correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
        (Enclosure.sfrac false 12 1))
      (p18505 (Eq.refl true) (Eq.refl true)
        (p18286 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p18857 (Eq.refl true)))

noncomputable def p18889 :=
p18595
  (p18596
    (@Enclosure.Real.IsNear.neg p18510 false 12062036528998723
      1125899906842624 30439 1125899906842624
      (p18628 (Eq.refl true))))
  (p18637
    (@p18646 p18631 p18594 p18873
      (p18879 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true))
    (p18888 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p18890 :=
@p18577 p18569
  (@p18589 false p18573 p18574 p18575
    p18576
    (BSN.iteratedDeriv_three_correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
        (Enclosure.sfrac false 12 1))
      (p18505 (Eq.refl true) (Eq.refl true)
        (p18286 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p18889 (Eq.refl true)))

noncomputable def p18891 :=
@p18567 p18568 p18569 1349014843 17179869184
  1 17179869184 p18498 p18475 p18499
  p18477
  (@p18571 p18566 p18568 p18569
    (BSN.correctionLinear_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p18283
        (Enclosure.sfrac false 12 1)))
    (@Enclosure.Real.IsNear.neg p18570 false p18565 p18566
      p18568 p18569
      (p18890 d244 (Eq.refl true))))

noncomputable def p18892 :=
@Enclosure.Real.IsNear.recentre' (@Inv.inv.{0} Real Real.instInv p18283) false
  1349014843 17179869184 1 17179869184 1349014843
  17179869184

noncomputable def p18893 :=
@Enclosure.Real.IsNear.inv_image p18283 218787737445 17179869184 41
  17179869184 674507421 674507422 8589934592
  (p18493 (Eq.refl true)) (Eq.refl true) (Eq.refl true)

noncomputable def p18894 :=
p18564
  (p18891
    (@p18892 1 17179869184
      (p18893 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (Eq.refl true))
    (Eq.refl true))

noncomputable def p18895 :=
@p18478 p18278
  (@p18480 17179869184
    (@p2563 1 0 1
      (BSN.neg_one_pow_even_mk 12 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1))
    p18496 (Eq.refl true))
  (p18894 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p18896 :=
@p18285 p18275 p18277 p18278
  (BSN.hardyZApproximantRS_eq
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
      true 5)
    12
    (p18286 (Eq.refl true) (Eq.refl true)
      (Eq.refl true)))
  (p18472 p18895 (Eq.refl true) (Eq.refl true))

theorem d245 : p18276 p18277 p18278 :=
@p18279 p18275 p18277 p18278
  (@Eq.refl.{1} Real
    (hardyZApproximantRS
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
        true 5)))
  p18896

noncomputable def p18897 :=
Enclosure.Real.IsNear
  (hardyZErrorBoundRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
      true 5))
  false 5945642289 549755813888

noncomputable def p18898 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Real.sqrt p17685)
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p18899 :=
@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 25 4) (@Inv.inv.{0} Real Real.instInv p18898))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 1 32)
    (@Inv.inv.{0} Real Real.instInv
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p18898
          p18898)
        p18898)))

noncomputable def p18900 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZErrorBoundRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
      true 5))
  p18899 false 5945642289

noncomputable def p18901 :=
BSN.hardyZErrorBoundRS_mk
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
    true 5)
  101779600 100000
  (Enclosure.sfrac_ofScientific_eq 101779600 5 100000 (Eq.refl true))
  (Eq.refl true)

noncomputable def p18902 :=
@Enclosure.Real.IsNear.addLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 25 4) (@Inv.inv.{0} Real Real.instInv p18898))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 1 32)
    (@Inv.inv.{0} Real Real.instInv
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p18898
          p18898)
        p18898)))

noncomputable def p18903 :=
@p18902 743205275 68719476736 25 68719476736 89
  549755813888 1 549755813888 408581426959513288704 5945642289
  549755813888

noncomputable def p18904 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 25 4)
  (@Inv.inv.{0} Real Real.instInv p18898) 25 4 0 1
  29728211 17179869184

noncomputable def p18905 :=
@Enclosure.Real.IsNear.recentre' (@Inv.inv.{0} Real Real.instInv p18898) false 29728211
  17179869184 1 17179869184 29728211 17179869184

noncomputable def p18906 :=
nat_lit 42641336002889153944117613

noncomputable def p18907 :=
@Enclosure.Real.IsNear.mulLit_ff (Real.sqrt p17685)
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p18908 :=
@p18907 61290063379 17179869184 7 17179869184
  695730003397247 4294967296000 254449 4294967296000 p18906
  73786976294838206464000 20465305362285043

noncomputable def p18909 :=
@p18908 73786976294838206464000
  (p17887
    (p17896 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (p17891 (p17893 (Eq.refl true))) (Eq.refl true)

noncomputable def p18910 :=
@Enclosure.Real.IsNear.inv_image p18898 p18906 73786976294838206464000
  20465305362285043 73786976294838206464000 14864105 14864106
  8589934592 p18909 (Eq.refl true) (Eq.refl true)

noncomputable def p18911 :=
@p18903 201 549755813888
  (@p18904 1 17179869184 743205275 68719476736 25
    68719476736 (Enclosure.Real.IsNear.const false 25 4)
    (@p18905 1 17179869184
      (p18910 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (Eq.refl true))
    (Eq.refl true))

noncomputable def p18912 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 1 32)
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p18898
        p18898)
      p18898))
  1

noncomputable def p18913 :=
@p18912 32 0 1 89 17179869184 1
  17179869184 89 549755813888 1 549755813888

noncomputable def p18914 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p18898
        p18898)
      p18898))
  false

noncomputable def p18915 :=
nat_lit 77534039211842984089628359157603058916589037744852578353467474549812004265397

noncomputable def p18916 :=
@Enclosure.Real.IsNear.inv_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p18898
      p18898)
    p18898)
  p18915 p10376

noncomputable def p18917 :=
nat_lit 111635183458777274739403393080977458491462159537675715676504383251019

noncomputable def p18918 :=
nat_lit 1818283536111290768182035929414746359261645176817769

noncomputable def p18919 :=
nat_lit 1745335925128680051656503268707150427036567

noncomputable def p18920 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p18898
    p18898)
  p18898 p18918 p10380 p18919

noncomputable def p18921 :=
@Enclosure.Real.IsNear.mulLit_ff p18898 p18898 p18906
  73786976294838206464000 20465305362285043 73786976294838206464000
  p18906 73786976294838206464000 20465305362285043
  73786976294838206464000 p18918

noncomputable def p18922 :=
@p18920 p10380 p18906 73786976294838206464000
  20465305362285043 73786976294838206464000 p18915 p10376
  p18917 p10376
  (@p18921 p10380 p18919 p10380
    p18909 p18909 (Eq.refl true))
  p18909

noncomputable def p18923 :=
@p18916 p18917 p10376 44 45
  8589934592 (p18922 (Eq.refl true)) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p18924 :=
p18913 (Enclosure.Real.IsNear.const false 1 32)
  (@p18914 89 17179869184 1 17179869184 89
    17179869184 1 17179869184 (p18923 (Eq.refl true))
    (Eq.refl true))

theorem d246 : p18897 201 549755813888 :=
@p18900 549755813888 201 549755813888
  (p18901 (Eq.refl true))
  (p18911 (p18924 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p18925 :=
Enclosure.Real.IsNear
  (hardyZErrorBoundRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
      true 5))
  false 5936658289 549755813888

noncomputable def p18926 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Real.sqrt p18283)
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p18927 :=
@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 25 4) (@Inv.inv.{0} Real Real.instInv p18926))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 1 32)
    (@Inv.inv.{0} Real Real.instInv
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p18926
          p18926)
        p18926)))

noncomputable def p18928 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZErrorBoundRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
      true 5))
  p18927 false 5936658289

noncomputable def p18929 :=
BSN.hardyZErrorBoundRS_mk
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
    true 5)
  101902800 100000
  (Enclosure.sfrac_ofScientific_eq 101902800 5 100000 (Eq.refl true))
  (Eq.refl true)

noncomputable def p18930 :=
@Enclosure.Real.IsNear.addLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 25 4) (@Inv.inv.{0} Real Real.instInv p18926))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 1 32)
    (@Inv.inv.{0} Real Real.instInv
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p18926
          p18926)
        p18926)))

noncomputable def p18931 :=
@p18930 742082275 68719476736 25 68719476736 89
  549755813888 1 549755813888 407964051180517064704 5936658289
  549755813888

noncomputable def p18932 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 25 4)
  (@Inv.inv.{0} Real Real.instInv p18926) 25 4 0 1
  29683291 17179869184

noncomputable def p18933 :=
@Enclosure.Real.IsNear.recentre' (@Inv.inv.{0} Real Real.instInv p18926) false 29683291
  17179869184 1 17179869184 29683291 17179869184

noncomputable def p18934 :=
nat_lit 21352932615524416484490549

noncomputable def p18935 :=
@Enclosure.Real.IsNear.mulLit_ff (Real.sqrt p18283)
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p18936 :=
@p18935 30654301119 8589934592 3 8589934592
  696572155816971 4294967296000 254757 4294967296000 p18934
  36893488147419103232000 9899114258388267

noncomputable def p18937 :=
@p18936 36893488147419103232000
  (p18485
    (p18494 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (p18489 (p18491 (Eq.refl true))) (Eq.refl true)

noncomputable def p18938 :=
@Enclosure.Real.IsNear.inv_image p18926 p18934 36893488147419103232000
  9899114258388267 36893488147419103232000 14841645 14841646
  8589934592 p18937 (Eq.refl true) (Eq.refl true)

noncomputable def p18939 :=
@p18931 201 549755813888
  (@p18932 1 17179869184 742082275 68719476736 25
    68719476736 (Enclosure.Real.IsNear.const false 25 4)
    (@p18933 1 17179869184
      (p18938 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (Eq.refl true))
    (Eq.refl true))

noncomputable def p18940 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 1 32)
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p18926
        p18926)
      p18926))
  1

noncomputable def p18941 :=
@p18940 32 0 1 89 17179869184 1
  17179869184 89 549755813888 1 549755813888

noncomputable def p18942 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p18926
        p18926)
      p18926))
  false

noncomputable def p18943 :=
nat_lit 9735821182289831968012828701974109830678372086098106337857513000010176939149

noncomputable def p18944 :=
nat_lit 50216813883093446110686315385661331328818843555712276103168000000000

noncomputable def p18945 :=
@Enclosure.Real.IsNear.inv_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p18926
      p18926)
    p18926)
  p18943 p18944

noncomputable def p18946 :=
nat_lit 13540436069751015240449922964249409047951368884927579904751719103347

noncomputable def p18947 :=
nat_lit 455947731283126397936318783451916696219860070321401

noncomputable def p18948 :=
nat_lit 1361129467683753853853498429727072845824000000

noncomputable def p18949 :=
nat_lit 84550047904695141602758157106007038248091

noncomputable def p18950 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p18926
    p18926)
  p18926 p18947 p18948 p18949

noncomputable def p18951 :=
nat_lit 272225893536750770770699685945414569164800000

noncomputable def p18952 :=
@Enclosure.Real.IsNear.mulLit_ff p18926 p18926 p18934
  36893488147419103232000 9899114258388267 36893488147419103232000
  p18934 36893488147419103232000 9899114258388267
  36893488147419103232000 p18947

noncomputable def p18953 :=
@p18950 p18951 p18934 36893488147419103232000
  9899114258388267 36893488147419103232000 p18943 p18944
  p18946 p18944
  (@p18952 p18948 p18949 p18951
    p18937 p18937 (Eq.refl true))
  p18937

noncomputable def p18954 :=
@p18945 p18946 p18944 44 45
  8589934592 (p18953 (Eq.refl true)) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p18955 :=
p18941 (Enclosure.Real.IsNear.const false 1 32)
  (@p18942 89 17179869184 1 17179869184 89
    17179869184 1 17179869184 (p18954 (Eq.refl true))
    (Eq.refl true))

theorem d247 : p18925 201 549755813888 :=
@p18928 549755813888 201 549755813888
  (p18929 (Eq.refl true))
  (p18939 (p18955 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p18956 :=
@LE.le.{0} Real Real.instLE
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@OfNat.ofNat.{0} Real 32
      (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
    Real.pi)
  (@Prod.fst.{0, 0} Real Real (@NonemptyInterval.toProd.{0} Real Real.instLE d50))

noncomputable def p18957 :=
@OfNat.ofNat.{0} Real 254449
  (@instOfNatAtLeastTwo.{0} Real 254449
    (@AddMonoidWithOne.toNatCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real
            (@DivisionSemiring.toSemiring.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))))))
    (Mathlib.Meta.NormNum.instAtLeastTwo 254447))

noncomputable def p18958 :=
@OfNat.ofNat.{0} Real 250
  (@instOfNatAtLeastTwo.{0} Real 250
    (@AddMonoidWithOne.toNatCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real
            (@DivisionSemiring.toSemiring.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))))))
    (Mathlib.Meta.NormNum.instAtLeastTwo 248))

noncomputable def p18959 :=
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
    p18957 p18958)

noncomputable def p18960 :=
@congrArg.{1, 1} Real Prop (@Prod.fst.{0, 0} Real Real (@NonemptyInterval.toProd.{0} Real Real.instLE d50))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real
    (@instHDiv.{0} Real
      (@DivInvMonoid.toDiv.{0} Real
        (@GroupWithZero.toDivInvMonoid.{0} Real
          (@DivisionSemiring.toGroupWithZero.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p18957 p18958)

noncomputable def p18961 :=
p18960
  (@LE.le.{0} Real Real.instLE
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 32
        (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
      Real.pi))

noncomputable def p18962 :=
@Mathlib.Meta.NormNum.IsNNRat.to_eq.{0} Real
  (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)) 254449 250
  (@Prod.fst.{0, 0} Real Real (@NonemptyInterval.toProd.{0} Real Real.instLE d50)) p18957
  p18958
  (@Mathlib.Meta.NormNum.isNNRat_ofScientific_of_true.{0} Real
    (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)) 101779600
    5 254449 250
    (p301
      (p302 p4
        (@p303 254449 250
          (p307 (@Eq.refl.{1} Nat (Nat.mul 101779600 1))
            (@Eq.refl.{1} Nat 100000))))))
  (@Eq.refl.{1} Real p18957)

noncomputable def p18963 :=
@congrArg.{1, 1} Real Prop
  (@HDiv.hDiv.{0, 0, 0} Real Real Real
    (@instHDiv.{0} Real
      (@DivInvMonoid.toDiv.{0} Real
        (@GroupWithZero.toDivInvMonoid.{0} Real
          (@DivisionSemiring.toGroupWithZero.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p18957 p18958)

noncomputable def p18964 :=
@p18963
  (@HDiv.hDiv.{0, 0, 0} Real Real Real
    (@instHDiv.{0} Real
      (@DivInvMonoid.toDiv.{0} Real
        (@GroupWithZero.toDivInvMonoid.{0} Real
          (@DivisionSemiring.toGroupWithZero.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p18957 p18958)

noncomputable def p18965 :=
p18964
  (@LE.le.{0} Real Real.instLE
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 32
        (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
      Real.pi))

noncomputable def p18966 :=
@Mathlib.Meta.NormNum.IsNNRat.to_eq.{0} Real
  (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)) 254449 250
  (@HDiv.hDiv.{0, 0, 0} Real Real Real
    (@instHDiv.{0} Real
      (@DivInvMonoid.toDiv.{0} Real
        (@GroupWithZero.toDivInvMonoid.{0} Real
          (@DivisionSemiring.toGroupWithZero.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p18957 p18958)

noncomputable def p18967 :=
@Mathlib.Meta.NormNum.isNNRat_mul.{0} Real
  (@DivisionSemiring.toSemiring.{0} Real
    (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real (@Distrib.toMul.{0} Real (@instDistribOfSemiring.{0} Real Real.semiring))))
  p18957
  (@Inv.inv.{0} Real
    (@InvOneClass.toInv.{0} Real
      (@DivInvOneMonoid.toInvOneClass.{0} Real
        (@DivisionMonoid.toDivInvOneMonoid.{0} Real
          (@GroupWithZero.toDivisionMonoid.{0} Real
            (@DivisionSemiring.toGroupWithZero.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))))))
    p18958)

noncomputable def p18968 :=
@p18967 254449 1 254449 1 250 250
  1
  (@Eq.refl.{1} (Real → Real → Real)
    (@HMul.hMul.{0, 0, 0} Real Real Real
      (@instHMul.{0} Real (@Distrib.toMul.{0} Real (@instDistribOfSemiring.{0} Real Real.semiring)))))
  (@Mathlib.Meta.NormNum.IsNat.to_isNNRat.{0} Real
    (@DivisionSemiring.toSemiring.{0} Real
      (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))
    p18957 254449
    (@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
      (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
      p18957 254449
      (@Eq.refl.{1} Real
        (@OfNat.ofNat.{0} Real 254449
          (@instOfNatAtLeastTwo.{0} Real 254449
            (@AddMonoidWithOne.toNatCast.{0} Real
              (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 254447))))))

noncomputable def p18969 :=
@Mathlib.Meta.NormNum.isNNRat_inv_pos.{0} Real
  (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))
  (@FloorSemiring.instCharZero.{0} Real Real.semiring Real.partialOrder
    (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing))
  p18958 249 1
  (@Mathlib.Meta.NormNum.IsNat.to_isNNRat.{0} Real
    (@DivisionSemiring.toSemiring.{0} Real
      (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))
    p18958 250
    (@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
      (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
      p18958 250
      (@Eq.refl.{1} Real
        (@OfNat.ofNat.{0} Real 250
          (@instOfNatAtLeastTwo.{0} Real 250
            (@AddMonoidWithOne.toNatCast.{0} Real
              (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 248))))))

noncomputable def p18970 :=
@p18966 p18957 p18958
  (@Mathlib.Meta.NormNum.isNNRat_div.{0} Real
    (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)) p18957
    p18958 254449 250
    (p18968 p18969 (@Eq.refl.{1} Nat (Nat.mul 254449 1))
      (@Eq.refl.{1} Nat 250)))
  (@Eq.refl.{1} Real p18957)

noncomputable def p18971 :=
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
    p18957 p18958)

noncomputable def p18972 :=
@LT.lt.{0} Real
  (@Preorder.toLT.{0} Real (@PartialOrder.toPreorder.{0} Real (@LinearOrder.toPartialOrder.{0} Real Real.linearOrder)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real
    (@instHDiv.{0} Real
      (@DivInvMonoid.toDiv.{0} Real
        (@GroupWithZero.toDivInvMonoid.{0} Real
          (@DivisionSemiring.toGroupWithZero.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p18957 p18958)

noncomputable def p18973 :=
@HMul.hMul.{0, 0, 0} Real Real Real
  (@instHMul.{0} Real (@Distrib.toMul.{0} Real (@instDistribOfSemiring.{0} Real Real.semiring)))
  (@OfNat.ofNat.{0} Real 229249
    (@instOfNatAtLeastTwo.{0} Real 229249
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))))
      (@Nat.instAtLeastTwoHAddOfNat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) 229247
          (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
        (@instNeZeroNatHAdd_1 229247 (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))

noncomputable def p18974 :=
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
  p18957

noncomputable def p18975 :=
@HMul.hMul.{0, 0, 0} Real Real Real
  (@instHMul.{0} Real
    (@Distrib.toMul.{0} Real
      (@instDistribOfSemiring.{0} Real
        (@DivisionSemiring.toSemiring.{0} Real
          (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
  (@OfNat.ofNat.{0} Real 250
    (@instOfNatAtLeastTwo.{0} Real 250
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 248)))

noncomputable def p18976 :=
@HSub.hSub.{0, 0, 0} Real Real Real
  (@instHSub.{0} Real
    (@SubNegMonoid.toSub.{0} Real
      (@AddGroup.toSubNegMonoid.{0} Real
        (@AddGroupWithOne.toAddGroup.{0} Real
          (@Ring.toAddGroupWithOne.{0} Real
            (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField)))))))
  p18974
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real
          (@DivisionSemiring.toSemiring.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p3705 (p18975 Real.pi))

noncomputable def p18977 :=
@HAdd.hAdd.{0, 0, 0} Real Real Real
  (@instHAdd.{0} Real (@AddSemigroup.toAdd.{0} Real (@AddMonoid.toAddSemigroup.{0} Real Real.instAddMonoid)))
  (p18973
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
  p18976

noncomputable def p18978 :=
@HMul.hMul.{0, 0, 0} Real Real Real
  (@instHMul.{0} Real (@Distrib.toMul.{0} Real (@instDistribOfSemiring.{0} Real Real.semiring)))
  (@OfNat.ofNat.{0} Real 400
    (@instOfNatAtLeastTwo.{0} Real 400
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))))
      (@Nat.instAtLeastTwoHAddOfNat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) 398
          (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
        (@instNeZeroNatHAdd_1 398 (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))

noncomputable def p18979 :=
@Eq.mp.{0}
  (@LT.lt.{0} Real (@Preorder.toLT.{0} Real (@PartialOrder.toPreorder.{0} Real Real.partialOrder))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real (@AddSemigroup.toAdd.{0} Real (@AddMonoid.toAddSemigroup.{0} Real Real.instAddMonoid)))
      p18977 (p18978 p3713))
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real (@MulZeroClass.toZero.{0} Real (@instMulZeroClassOfSemiring.{0} Real Real.semiring)))))
  (@LT.lt.{0} Real (@Preorder.toLT.{0} Real (@PartialOrder.toPreorder.{0} Real Real.partialOrder))
    (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real (@MulZeroClass.toZero.{0} Real (@instMulZeroClassOfSemiring.{0} Real Real.semiring)))))

noncomputable def p18980 :=
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
    (Int.negOfNat 8000))

noncomputable def p18981 :=
@Mathlib.Tactic.Ring.Common.add_congr.{0} Real Real.instCommSemiring p18977
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@Mathlib.Meta.NormNum.instAddMonoidWithOne.{0} Real
        (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)))
      25200)
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p18980
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))
  (p18978 p3713)

noncomputable def p18982 :=
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
    8000)

noncomputable def p18983 :=
@p18981
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 25200))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p18982
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))

noncomputable def p18984 :=
@Mathlib.Tactic.Ring.Common.add_congr.{0} Real Real.instCommSemiring
  (p18973
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
      (Int.negOfNat 229249))
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))

noncomputable def p18985 :=
@p18984 p18976
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      254449)
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p18980
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
      25200)
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p18980
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))

noncomputable def p18986 :=
@Mathlib.Tactic.Ring.Common.mul_congr.{0} Real Real.instCommSemiring
  (@OfNat.ofNat.{0} Real 229249
    (@instOfNatAtLeastTwo.{0} Real 229249
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))))
      (@Nat.instAtLeastTwoHAddOfNat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) 229247
          (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
        (@instNeZeroNatHAdd_1 229247 (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))

noncomputable def p18987 :=
@p18986
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      229249)
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

noncomputable def p18988 :=
@Mathlib.Tactic.Ring.cast_pos.{0} Real Real.instCommSemiring
  (@OfNat.ofNat.{0} Real 229249
    (@instOfNatAtLeastTwo.{0} Real 229249
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))))
      (@Nat.instAtLeastTwoHAddOfNat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) 229247
          (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
        (@instNeZeroNatHAdd_1 229247 (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))

noncomputable def p18989 :=
@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
  (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
  (@OfNat.ofNat.{0} Real 229249
    (@instOfNatAtLeastTwo.{0} Real 229249
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))))
      (@Nat.instAtLeastTwoHAddOfNat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) 229247
          (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
        (@instNeZeroNatHAdd_1 229247 (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))

noncomputable def p18990 :=
@p18987
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
      (Int.negOfNat 229249))
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@p18988 229249
    (@p18989 229249
      (@Eq.refl.{1} Real
        (@OfNat.ofNat.{0} Real 229249
          (@instOfNatAtLeastTwo.{0} Real 229249
            (@AddMonoidWithOne.toNatCast.{0} Real
              (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 229247))))))

noncomputable def p18991 :=
@Mathlib.Tactic.Ring.Common.add_mul.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    229249)
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
      (Int.negOfNat 229249))
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))

noncomputable def p18992 :=
@Mathlib.Tactic.Ring.Common.mul_add.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    229249)
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 1))
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 229249))

noncomputable def p18993 :=
@Mathlib.Meta.NormNum.IsInt.to_raw_eq.{0} Real
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      229249)
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 1)))
  (Int.negOfNat 229249)

noncomputable def p18994 :=
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
    229249)
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 1))

noncomputable def p18995 :=
@p18994 (Int.ofNat 229249) (Int.negOfNat 1) (Int.negOfNat 229249)
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
      229249)
    229249
    (@Mathlib.Meta.NormNum.IsNat.of_raw.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      229249))

noncomputable def p18996 :=
@p18992
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 229249))
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@p18993 (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (p18995
      (@Mathlib.Meta.NormNum.IsInt.of_raw.{0} Real
        (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)) (Int.negOfNat 1))
      (@Eq.refl.{1} Int (Int.negOfNat 229249))))
  (@Mathlib.Tactic.Ring.Common.mul_zero.{0} Real Real.instCommSemiring
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      229249))

noncomputable def p18997 :=
@p18991
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 229249))
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (p18996
    (@Mathlib.Tactic.Ring.Common.add_pf_add_zero.{0} Real Real.instCommSemiring
      (@HAdd.hAdd.{0, 0, 0} Real Real Real
        (@instHAdd.{0} Real
          (@Distrib.toAdd.{0} Real
            (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
        (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
          (Int.negOfNat 229249))
        (@OfNat.ofNat.{0} Real 0
          (@Zero.toOfNat0.{0} Real
            (@MulZeroClass.toZero.{0} Real
              (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))))

noncomputable def p18998 :=
p18997
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
        (Int.negOfNat 229249))
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))

noncomputable def p18999 :=
p18985
  (p18990
    (p3726 p3727
      (p3728
        (@Mathlib.Meta.NormNum.IsInt.to_raw_eq.{0} Real p3729 (Int.negOfNat 1)
          (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
          (p3733 (@Eq.refl.{1} Int (Int.negOfNat 1))))
        (@Mathlib.Tactic.Ring.Common.neg_zero.{0} Real Real.commRing)))
    p18998)

noncomputable def p19000 :=
@Mathlib.Tactic.Ring.Common.sub_congr.{0} Real Real.commRing p18974
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      254449)
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
    p3705 (p18975 Real.pi))

noncomputable def p19001 :=
@p3744 p18957
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      254449)
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
      254449)
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))

noncomputable def p19002 :=
p19001
  (p3746
    (p3747
      (@Nat.cast_one.{0} Real
        (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))))
  (@Mathlib.Tactic.Ring.cast_pos.{0} Real Real.instCommSemiring p18957 254449
    (@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
      (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
      p18957 254449
      (@Eq.refl.{1} Real
        (@OfNat.ofNat.{0} Real 254449
          (@instOfNatAtLeastTwo.{0} Real 254449
            (@AddMonoidWithOne.toNatCast.{0} Real
              (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 254447))))))

noncomputable def p19003 :=
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
      254449)
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
      254449)
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))

noncomputable def p19004 :=
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
    254449)
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    254449)

noncomputable def p19005 :=
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
      254449))
  254449

noncomputable def p19006 :=
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
    254449)
  1 254449

noncomputable def p19007 :=
@p19006 254449
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
    254449)
  (@Eq.refl.{1} Nat 254449)

noncomputable def p19008 :=
@p19004
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
      254449)
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@p19005
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p19007)

noncomputable def p19009 :=
p19008
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
        254449)
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))

noncomputable def p19010 :=
@p19003
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
      254449)
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  p19009

noncomputable def p19011 :=
p19010
  (@Mathlib.Tactic.Ring.Common.zero_mul.{0} Real Real.instCommSemiring
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      (@Nat.rawCast.{0} Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
            (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
        254449)
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))

noncomputable def p19012 :=
p19011
  (@Mathlib.Tactic.Ring.Common.add_pf_add_zero.{0} Real Real.instCommSemiring
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      (@Nat.rawCast.{0} Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
            (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
        254449)
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))

noncomputable def p19013 :=
@p19000
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p18982
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
      254449)
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p18980
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))
  (p19002 p19012)

noncomputable def p19014 :=
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
  (p18975 Real.pi)

noncomputable def p19015 :=
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
    250)

noncomputable def p19016 :=
@p19014
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p19015
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p18982
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

noncomputable def p19017 :=
@Mathlib.Tactic.Ring.Common.mul_congr.{0} Real Real.instCommSemiring
  (@OfNat.ofNat.{0} Real 250
    (@instOfNatAtLeastTwo.{0} Real 250
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 248)))

noncomputable def p19018 :=
@p19017
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      250)
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  Real.pi

noncomputable def p19019 :=
@Mathlib.Tactic.Ring.cast_pos.{0} Real Real.instCommSemiring
  (@OfNat.ofNat.{0} Real 250
    (@instOfNatAtLeastTwo.{0} Real 250
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 248)))

noncomputable def p19020 :=
@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
  (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
  (@OfNat.ofNat.{0} Real 250
    (@instOfNatAtLeastTwo.{0} Real 250
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 248)))

noncomputable def p19021 :=
@p19018
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
    p19015
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@p19019 250
    (@p19020 250
      (@Eq.refl.{1} Real
        (@OfNat.ofNat.{0} Real 250
          (@instOfNatAtLeastTwo.{0} Real 250
            (@AddMonoidWithOne.toNatCast.{0} Real
              (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 248))))))

noncomputable def p19022 :=
p19021
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

noncomputable def p19023 :=
@Mathlib.Tactic.Ring.Common.add_mul.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    250)
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
    p19015
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))

noncomputable def p19024 :=
@Mathlib.Tactic.Ring.Common.mul_add.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    250)
  p3777
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  p19015

noncomputable def p19025 :=
@Mathlib.Tactic.Ring.Common.mul_pf_right.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    250)
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1)
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    250)
  Real.pi

noncomputable def p19026 :=
@Mathlib.Meta.NormNum.IsNat.to_raw_eq.{0} Real
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      250)
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      1))
  250

noncomputable def p19027 :=
@Mathlib.Meta.NormNum.isNat_mul.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    250)
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1)
  250 1

noncomputable def p19028 :=
@p19027 250
  (@Eq.refl.{1} (Real → Real → Real)
    (@HMul.hMul.{0, 0, 0} Real Real Real
      (@instHMul.{0} Real
        (@Distrib.toMul.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@Mathlib.Meta.NormNum.IsNat.of_raw.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    250)
  (@Mathlib.Meta.NormNum.IsNat.of_raw.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1)
  (@Eq.refl.{1} Nat 250)

noncomputable def p19029 :=
@p19024
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p19015
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (p19025
    (@Nat.rawCast.{0} Nat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat
          (@Semiring.toNonAssocSemiring.{0} Nat (@CommSemiring.toSemiring.{0} Nat Nat.instCommSemiring))))
      1)
    (@p19026
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p19028))
  (@Mathlib.Tactic.Ring.Common.mul_zero.{0} Real Real.instCommSemiring
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      250))

noncomputable def p19030 :=
@p19023
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p19015
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (p19029
    (@Mathlib.Tactic.Ring.Common.add_pf_add_zero.{0} Real Real.instCommSemiring
      (@HAdd.hAdd.{0, 0, 0} Real Real Real
        (@instHAdd.{0} Real
          (@Distrib.toAdd.{0} Real
            (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
        p19015
        (@OfNat.ofNat.{0} Real 0
          (@Zero.toOfNat0.{0} Real
            (@MulZeroClass.toZero.{0} Real
              (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))))

noncomputable def p19031 :=
p19030
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
      p19015
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))

noncomputable def p19032 :=
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
    p19015
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p18982
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))

noncomputable def p19033 :=
@Mathlib.Tactic.Ring.Common.mul_add.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    32)
  p19015
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  p18982

noncomputable def p19034 :=
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
    250)
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    8000)
  Real.pi

noncomputable def p19035 :=
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
      250))
  8000

noncomputable def p19036 :=
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
    250)
  32 250

noncomputable def p19037 :=
@p19036 8000
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
    250)
  (@Eq.refl.{1} Nat 8000)

noncomputable def p19038 :=
@p19033
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p18982
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (p19034
    (@Nat.rawCast.{0} Nat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat
          (@Semiring.toNonAssocSemiring.{0} Nat (@CommSemiring.toSemiring.{0} Nat Nat.instCommSemiring))))
      1)
    (@p19035
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p19037))
  (@Mathlib.Tactic.Ring.Common.mul_zero.{0} Real Real.instCommSemiring
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      32))

noncomputable def p19039 :=
@p19032
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p18982
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (p19038
    (@Mathlib.Tactic.Ring.Common.add_pf_add_zero.{0} Real Real.instCommSemiring
      (@HAdd.hAdd.{0, 0, 0} Real Real Real
        (@instHAdd.{0} Real
          (@Distrib.toAdd.{0} Real
            (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
        p18982
        (@OfNat.ofNat.{0} Real 0
          (@Zero.toOfNat0.{0} Real
            (@MulZeroClass.toZero.{0} Real
              (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))))

noncomputable def p19040 :=
p19039
  (@Mathlib.Tactic.Ring.Common.zero_mul.{0} Real Real.instCommSemiring
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p19015
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))
  (@Mathlib.Tactic.Ring.Common.add_pf_add_zero.{0} Real Real.instCommSemiring
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p18982
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))

noncomputable def p19041 :=
@Mathlib.Tactic.Ring.Common.sub_pf.{0} Real Real.commRing
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      254449)
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p18982
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))

noncomputable def p19042 :=
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
    8000)

noncomputable def p19043 :=
@p3730
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    8000)
  (Int.ofNat 8000) (Int.negOfNat 8000) p3731

noncomputable def p19044 :=
p19043
  (@Mathlib.Meta.NormNum.IsNat.to_isInt.{0} Real
    (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      8000)
    8000
    (@Mathlib.Meta.NormNum.IsNat.of_raw.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      8000))

noncomputable def p19045 :=
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
    8000)
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 8000))
  (@Mathlib.Meta.NormNum.IsInt.to_raw_eq.{0} Real p19042 (Int.negOfNat 8000)
    (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (p19044 (@Eq.refl.{1} Int (Int.negOfNat 8000))))

noncomputable def p19046 :=
@Mathlib.Tactic.Ring.Common.neg_add.{0} Real Real.commRing p18982
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  p18980
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  p19045 (@Mathlib.Tactic.Ring.Common.neg_zero.{0} Real Real.commRing)

noncomputable def p19047 :=
@p19041
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p18980
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
      254449)
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p18980
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))
  p19046

noncomputable def p19048 :=
@Mathlib.Tactic.Ring.Common.add_pf_add_lt.{0} Real Real.instCommSemiring
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p18980
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p18980
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    254449)

noncomputable def p19049 :=
p19047
  (p19048
    (@Mathlib.Tactic.Ring.Common.add_pf_zero_add.{0} Real Real.instCommSemiring
      (@HAdd.hAdd.{0, 0, 0} Real Real Real
        (@instHAdd.{0} Real
          (@Distrib.toAdd.{0} Real
            (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
        p18980
        (@OfNat.ofNat.{0} Real 0
          (@Zero.toOfNat0.{0} Real
            (@MulZeroClass.toZero.{0} Real
              (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))))

noncomputable def p19050 :=
@Mathlib.Tactic.Ring.Common.add_pf_add_overlap.{0} Real Real.instCommSemiring
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 229249))
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    254449)
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p18980
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@Nat.rawCast.{0} Real
    (@Mathlib.Meta.NormNum.instAddMonoidWithOne.{0} Real
      (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)))
    25200)
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p18980
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))

noncomputable def p19051 :=
@Mathlib.Meta.NormNum.IsNat.to_raw_eq.{0} Real
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 229249))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      254449))
  25200
  (@Mathlib.Meta.NormNum.instAddMonoidWithOne.{0} Real
    (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)))

noncomputable def p19052 :=
@Mathlib.Meta.NormNum.isInt_add.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 229249))
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    254449)
  (Int.negOfNat 229249) (Int.ofNat 254449)

noncomputable def p19053 :=
@p19052 (Int.ofNat 25200)
  (@Eq.refl.{1} (Real → Real → Real)
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@Mathlib.Meta.NormNum.IsInt.of_raw.{0} Real
    (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)) (Int.negOfNat 229249))
  (@Mathlib.Meta.NormNum.IsNat.to_isInt.{0} Real
    (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      254449)
    254449
    (@Mathlib.Meta.NormNum.IsNat.of_raw.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      254449))

noncomputable def p19054 :=
@Mathlib.Meta.NormNum.IsInt.to_isNat.{0} Real
  (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 229249))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      254449))
  25200 (p19053 (@Eq.refl.{1} Int (Int.ofNat 25200)))

noncomputable def p19055 :=
p18999
  (p19013
    (p19016 (p19022 p19031) p19040)
    p19049)
  (p19050 (p19051 p19054)
    (@Mathlib.Tactic.Ring.Common.add_pf_zero_add.{0} Real Real.instCommSemiring
      (@HAdd.hAdd.{0, 0, 0} Real Real Real
        (@instHAdd.{0} Real
          (@Distrib.toAdd.{0} Real
            (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
        p18980
        (@OfNat.ofNat.{0} Real 0
          (@Zero.toOfNat0.{0} Real
            (@MulZeroClass.toZero.{0} Real
              (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))))

noncomputable def p19056 :=
@Mathlib.Tactic.Ring.Common.mul_congr.{0} Real Real.instCommSemiring
  (@OfNat.ofNat.{0} Real 400
    (@instOfNatAtLeastTwo.{0} Real 400
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))))
      (@Nat.instAtLeastTwoHAddOfNat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) 398
          (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
        (@instNeZeroNatHAdd_1 398 (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))

noncomputable def p19057 :=
@p19056
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      400)
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  p3713

noncomputable def p19058 :=
@p19057
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
      (Int.negOfNat 25200))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p18982
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))

noncomputable def p19059 :=
@Mathlib.Tactic.Ring.cast_pos.{0} Real Real.instCommSemiring
  (@OfNat.ofNat.{0} Real 400
    (@instOfNatAtLeastTwo.{0} Real 400
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))))
      (@Nat.instAtLeastTwoHAddOfNat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) 398
          (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
        (@instNeZeroNatHAdd_1 398 (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))

noncomputable def p19060 :=
@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
  (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
  (@OfNat.ofNat.{0} Real 400
    (@instOfNatAtLeastTwo.{0} Real 400
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))))
      (@Nat.instAtLeastTwoHAddOfNat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) 398
          (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
        (@instNeZeroNatHAdd_1 398 (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))

noncomputable def p19061 :=
p19058
  (@p19059 400
    (@p19060 400
      (@Eq.refl.{1} Real
        (@OfNat.ofNat.{0} Real 400
          (@instOfNatAtLeastTwo.{0} Real 400
            (@AddMonoidWithOne.toNatCast.{0} Real
              (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 398))))))

noncomputable def p19062 :=
@Mathlib.Tactic.Ring.Common.add_mul.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    400)
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
      (Int.negOfNat 25200))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p18982
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))

noncomputable def p19063 :=
@Mathlib.Tactic.Ring.Common.mul_add.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    400)
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
    (Int.negOfNat 25200))

noncomputable def p19064 :=
@Mathlib.Meta.NormNum.IsInt.to_raw_eq.{0} Real
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      400)
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 63)))
  (Int.negOfNat 25200)

noncomputable def p19065 :=
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
    400)
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 63))

noncomputable def p19066 :=
@p19065 (Int.ofNat 400) (Int.negOfNat 63) (Int.negOfNat 25200)
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
      400)
    400
    (@Mathlib.Meta.NormNum.IsNat.of_raw.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      400))

noncomputable def p19067 :=
@p19063
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p18982
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 25200))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p18982
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))
  (@p19064 (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (p19066
      (@Mathlib.Meta.NormNum.IsInt.of_raw.{0} Real
        (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)) (Int.negOfNat 63))
      (@Eq.refl.{1} Int (Int.negOfNat 25200))))

noncomputable def p19068 :=
@Mathlib.Tactic.Ring.Common.mul_add.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    400)
  p3819
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  p18982

noncomputable def p19069 :=
@Mathlib.Tactic.Ring.Common.mul_pf_right.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    400)
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    20)
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    8000)
  Real.pi

noncomputable def p19070 :=
@Mathlib.Meta.NormNum.IsNat.to_raw_eq.{0} Real
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      400)
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      20))
  8000

noncomputable def p19071 :=
@Mathlib.Meta.NormNum.isNat_mul.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    400)
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    20)
  400 20

noncomputable def p19072 :=
@p19071 8000
  (@Eq.refl.{1} (Real → Real → Real)
    (@HMul.hMul.{0, 0, 0} Real Real Real
      (@instHMul.{0} Real
        (@Distrib.toMul.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@Mathlib.Meta.NormNum.IsNat.of_raw.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    400)
  (@Mathlib.Meta.NormNum.IsNat.of_raw.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    20)
  (@Eq.refl.{1} Nat 8000)

noncomputable def p19073 :=
@p19068
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p18982
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (p19069
    (@Nat.rawCast.{0} Nat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat
          (@Semiring.toNonAssocSemiring.{0} Nat (@CommSemiring.toSemiring.{0} Nat Nat.instCommSemiring))))
      1)
    (@p19070
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p19072))
  (@Mathlib.Tactic.Ring.Common.mul_zero.{0} Real Real.instCommSemiring
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      400))

noncomputable def p19074 :=
p19067
  (p19073
    (@Mathlib.Tactic.Ring.Common.add_pf_add_zero.{0} Real Real.instCommSemiring
      (@HAdd.hAdd.{0, 0, 0} Real Real Real
        (@instHAdd.{0} Real
          (@Distrib.toAdd.{0} Real
            (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
        p18982
        (@OfNat.ofNat.{0} Real 0
          (@Zero.toOfNat0.{0} Real
            (@MulZeroClass.toZero.{0} Real
              (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))))

noncomputable def p19075 :=
@Mathlib.Tactic.Ring.Common.add_pf_add_lt.{0} Real Real.instCommSemiring
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p18982
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p18982
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 25200))

noncomputable def p19076 :=
p19074
  (p19075
    (@Mathlib.Tactic.Ring.Common.add_pf_zero_add.{0} Real Real.instCommSemiring
      (@HAdd.hAdd.{0, 0, 0} Real Real Real
        (@instHAdd.{0} Real
          (@Distrib.toAdd.{0} Real
            (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
        p18982
        (@OfNat.ofNat.{0} Real 0
          (@Zero.toOfNat0.{0} Real
            (@MulZeroClass.toZero.{0} Real
              (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))))

noncomputable def p19077 :=
@p19062
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 25200))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p18982
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))
  p19076

noncomputable def p19078 :=
p19077
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

noncomputable def p19079 :=
p19078
  (@Mathlib.Tactic.Ring.Common.add_pf_add_zero.{0} Real Real.instCommSemiring
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
        (Int.negOfNat 25200))
      (@HAdd.hAdd.{0, 0, 0} Real Real Real
        (@instHAdd.{0} Real
          (@Distrib.toAdd.{0} Real
            (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
        p18982
        (@OfNat.ofNat.{0} Real 0
          (@Zero.toOfNat0.{0} Real
            (@MulZeroClass.toZero.{0} Real
              (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))))

noncomputable def p19080 :=
@Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@Mathlib.Meta.NormNum.instAddMonoidWithOne.{0} Real
      (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)))
    25200)
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p18980
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 25200))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p18982
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))

noncomputable def p19081 :=
@Mathlib.Meta.NormNum.isInt_add.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@Nat.rawCast.{0} Real
    (@Mathlib.Meta.NormNum.instAddMonoidWithOne.{0} Real
      (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)))
    25200)
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 25200))
  (Int.ofNat 25200) (Int.negOfNat 25200)

noncomputable def p19082 :=
@p19081 (Int.ofNat 0)
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
      25200)
    25200
    (@Mathlib.Meta.NormNum.IsNat.of_raw.{0} Real
      (@Mathlib.Meta.NormNum.instAddMonoidWithOne.{0} Real
        (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)))
      25200))
  (@Mathlib.Meta.NormNum.IsInt.of_raw.{0} Real
    (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)) (Int.negOfNat 25200))

noncomputable def p19083 :=
@Mathlib.Meta.NormNum.IsInt.to_isNat.{0} Real
  (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@Mathlib.Meta.NormNum.instAddMonoidWithOne.{0} Real
        (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)))
      25200)
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 25200)))
  0 (p19082 (@Eq.refl.{1} Int (Int.ofNat 0)))

noncomputable def p19084 :=
@Mathlib.Meta.NormNum.isInt_add.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 8000))
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    8000)
  (Int.negOfNat 8000) (Int.ofNat 8000)

noncomputable def p19085 :=
@p19084 (Int.ofNat 0)
  (@Eq.refl.{1} (Real → Real → Real)
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@Mathlib.Meta.NormNum.IsInt.of_raw.{0} Real
    (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)) (Int.negOfNat 8000))
  (@Mathlib.Meta.NormNum.IsNat.to_isInt.{0} Real
    (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      8000)
    8000
    (@Mathlib.Meta.NormNum.IsNat.of_raw.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      8000))

noncomputable def p19086 :=
@Mathlib.Meta.NormNum.IsInt.to_isNat.{0} Real
  (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 8000))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      8000))
  0 (p19085 (@Eq.refl.{1} Int (Int.ofNat 0)))

noncomputable def p19087 :=
@Mathlib.Tactic.Ring.Common.add_overlap_pf_zero.{0} Real Real.instCommSemiring
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 8000))
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    8000)
  Real.pi
  (@Nat.rawCast.{0} Nat
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat
        (@Semiring.toNonAssocSemiring.{0} Nat (@CommSemiring.toSemiring.{0} Nat Nat.instCommSemiring))))
    1)
  p19086

noncomputable def p19088 :=
@Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero.{0} Real Real.instCommSemiring p18980
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  p18982
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  p19087

noncomputable def p19089 :=
@Mathlib.Tactic.Ring.of_eq.{1} Real
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real (@AddSemigroup.toAdd.{0} Real (@AddMonoid.toAddSemigroup.{0} Real Real.instAddMonoid)))
    p18977 (p18978 p3713))
  (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (p18983 p19055
    (p19061
      (p3840 (p3842 p3852) p3860)
      p19079)
    (@p19080
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
      p19083
      (p19088
        (@Mathlib.Tactic.Ring.Common.add_pf_zero_add.{0} Real Real.instCommSemiring
          (@OfNat.ofNat.{0} Real 0
            (@Zero.toOfNat0.{0} Real
              (@MulZeroClass.toZero.{0} Real
                (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))))

noncomputable def p19090 :=
@congrArg.{1, 1} Real Prop
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real (@AddSemigroup.toAdd.{0} Real (@AddMonoid.toAddSemigroup.{0} Real Real.instAddMonoid)))
    p18977 (p18978 p3713))
  (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
  (fun (_a : Real) =>
    @LT.lt.{0} Real (@Preorder.toLT.{0} Real (@PartialOrder.toPreorder.{0} Real Real.partialOrder)) _a
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real (@MulZeroClass.toZero.{0} Real (@instMulZeroClassOfSemiring.{0} Real Real.semiring)))))
  (p19089
    (@Mathlib.Tactic.Ring.cast_zero.{0} Real Real.instCommSemiring
      (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
      (@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
        (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
        (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) 0
        (@Nat.cast_zero.{0} Real
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))))))

noncomputable def p19091 :=
@HAdd.hAdd.{0, 0, 0} Real Real Real
  (@instHAdd.{0} Real (@Distrib.toAdd.{0} Real (@instDistribOfSemiring.{0} Real Real.semiring)))
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real (@instDistribOfSemiring.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))))
    (@OfNat.ofNat.{0} Real 229249
      (@instOfNatAtLeastTwo.{0} Real 229249 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 229248 (instOfNatNat 229248))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 229247 (instOfNatNat 229247))))))
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
  p18976

noncomputable def p19092 :=
@Mathlib.Tactic.Linarith.add_neg.{0} Real Real.semiring Real.partialOrder Real.instIsStrictOrderedRing
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real (@instDistribOfSemiring.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))))
    (@OfNat.ofNat.{0} Real 229249
      (@instOfNatAtLeastTwo.{0} Real 229249 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 229248 (instOfNatNat 229248))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 229247 (instOfNatNat 229247))))))
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
  p18976

noncomputable def p19093 :=
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
  (@OfNat.ofNat.{0} Real 229249
    (@instOfNatAtLeastTwo.{0} Real 229249 Real.instNatCast
      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 229248 (instOfNatNat 229248))
        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 229247 (instOfNatNat 229247))))))
  (@neg_neg_of_pos.{0} Real Real.instAddCommGroup Real.partialOrder Real.instIsOrderedAddMonoid
    (@OfNat.ofNat.{0} Real 1
      (@One.toOfNat1.{0} Real
        (@AddMonoidWithOne.toOne.{0} Real
          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
            (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
              (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))))))
    (@Mathlib.Tactic.Linarith.zero_lt_one.{0} Real Real.semiring Real.partialOrder Real.instIsStrictOrderedRing))

noncomputable def p19094 :=
@Mathlib.Meta.NormNum.isNat_lt_true.{0} Real Real.semiring Real.partialOrder Real.instIsOrderedRing
  (@FloorSemiring.instCharZero.{0} Real (@Ring.toSemiring.{0} Real Real.instRing) Real.partialOrder
    (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing))
  (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
  (@OfNat.ofNat.{0} Real 229249
    (@instOfNatAtLeastTwo.{0} Real 229249 Real.instNatCast
      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 229248 (instOfNatNat 229248))
        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 229247 (instOfNatNat 229247))))))
  0 229249
  (@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
    (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
    (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) 0
    (@Nat.cast_zero.{0} Real
      (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))))

noncomputable def p19095 :=
p19094
  (@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
    (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
    (@OfNat.ofNat.{0} Real 229249
      (@instOfNatAtLeastTwo.{0} Real 229249 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 229248 (instOfNatNat 229248))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 229247 (instOfNatNat 229247))))))
    229249
    (@Eq.refl.{1} Real
      (@OfNat.ofNat.{0} Real 229249
        (@instOfNatAtLeastTwo.{0} Real 229249
          (@AddMonoidWithOne.toNatCast.{0} Real
            (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
          (Mathlib.Meta.NormNum.instAtLeastTwo 229247)))))

noncomputable def p19096 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (@OfNat.ofNat.{0} Real 250
    (@instOfNatAtLeastTwo.{0} Real 250
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 248)))

noncomputable def p19097 :=
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
    p18957 p18958)

noncomputable def p19098 :=
p19096
  (p19097
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 32
        (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
      Real.pi))

noncomputable def p19099 :=
@Mathlib.Tactic.CancelDenoms.derive_trans.{0} Real Real.instMul
  (p19097
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 32
        (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
      Real.pi))

noncomputable def p19100 :=
@p19099
  (p19097
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 32
        (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
      Real.pi))

noncomputable def p19101 :=
@p19100
  (@OfNat.ofNat.{0} Real 250
    (@instOfNatAtLeastTwo.{0} Real 250
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 248)))

noncomputable def p19102 :=
@congrArg.{1, 1} Real (Real → Real)
  (@HDiv.hDiv.{0, 0, 0} Real Real Real
    (@instHDiv.{0} Real
      (@DivInvMonoid.toDiv.{0} Real
        (@GroupWithZero.toDivInvMonoid.{0} Real
          (@DivisionSemiring.toGroupWithZero.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p18957 p18958)

noncomputable def p19103 :=
@p19102
  (@HDiv.hDiv.{0, 0, 0} Real Real Real
    (@instHDiv.{0} Real
      (@DivInvMonoid.toDiv.{0} Real
        (@GroupWithZero.toDivInvMonoid.{0} Real
          (@DivisionSemiring.toGroupWithZero.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p18957 p18958)

noncomputable def p19104 :=
@congrFun'.{1, 1} Real Real p19097 p19097
  (p19103
    (@HSub.hSub.{0, 0, 0} Real Real Real
      (@instHSub.{0} Real
        (@SubNegMonoid.toSub.{0} Real
          (@AddGroup.toSubNegMonoid.{0} Real
            (@AddGroupWithOne.toAddGroup.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))))))
    (p18970 (@Eq.refl.{1} Real p18958)))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@OfNat.ofNat.{0} Real 32
      (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
    Real.pi)

noncomputable def p19105 :=
@Mathlib.Tactic.CancelDenoms.sub_subst.{0} Real
  (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))
  (@OfNat.ofNat.{0} Real 250
    (@instOfNatAtLeastTwo.{0} Real 250
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 248)))

noncomputable def p19106 :=
@p19105
  (@HDiv.hDiv.{0, 0, 0} Real Real Real
    (@instHDiv.{0} Real
      (@DivInvMonoid.toDiv.{0} Real
        (@GroupWithZero.toDivInvMonoid.{0} Real
          (@DivisionSemiring.toGroupWithZero.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p18957 p18958)

noncomputable def p19107 :=
@p19106
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@OfNat.ofNat.{0} Real 32
      (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
    Real.pi)
  p18974

noncomputable def p19108 :=
@p19107
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real
          (@DivisionSemiring.toSemiring.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p3705 (p18975 Real.pi))

noncomputable def p19109 :=
@Mathlib.Tactic.CancelDenoms.div_subst.{0} Real Real.instField
  (@OfNat.ofNat.{0} Real 1
    (@One.toOfNat1.{0} Real
      (@AddMonoidWithOne.toOne.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))))
  (@OfNat.ofNat.{0} Real 250
    (@instOfNatAtLeastTwo.{0} Real 250
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 248)))

noncomputable def p19110 :=
@p19109
  (@OfNat.ofNat.{0} Real 250
    (@instOfNatAtLeastTwo.{0} Real 250
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 248)))

noncomputable def p19111 :=
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
  p18957

noncomputable def p19112 :=
@HDiv.hDiv.{0, 0, 0} Real Real Real
  (@instHDiv.{0} Real
    (@DivInvMonoid.toDiv.{0} Real
      (@DivisionRing.toDivInvMonoid.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))
  (@OfNat.ofNat.{0} Real 250
    (@instOfNatAtLeastTwo.{0} Real 250
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 248)))

noncomputable def p19113 :=
@Mathlib.Meta.NormNum.isNat_eq_true.{0} Real
  (@Mathlib.Meta.NormNum.instAddMonoidWithOne'.{0} Real
    (@DivisionSemiring.toSemiring.{0} Real
      (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))
  (p19112 p18958)
  (@OfNat.ofNat.{0} Real 1
    (@One.toOfNat1.{0} Real
      (@AddMonoidWithOne.toOne.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))))
  1

noncomputable def p19114 :=
@Mathlib.Meta.NormNum.isNNRat_div.{0} Real
  (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))
  (@OfNat.ofNat.{0} Real 250
    (@instOfNatAtLeastTwo.{0} Real 250
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 248)))

noncomputable def p19115 :=
p18975
  (@Inv.inv.{0} Real
    (@InvOneClass.toInv.{0} Real
      (@DivInvOneMonoid.toInvOneClass.{0} Real
        (@DivisionMonoid.toDivInvOneMonoid.{0} Real
          (@GroupWithZero.toDivisionMonoid.{0} Real
            (@DivisionSemiring.toGroupWithZero.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))))))
    p18958)

noncomputable def p19116 :=
@HMul.hMul.{0, 0, 0} Real Real Real
  (@instHMul.{0} Real (@Distrib.toMul.{0} Real (@instDistribOfSemiring.{0} Real Real.semiring)))
  (@OfNat.ofNat.{0} Real 250
    (@instOfNatAtLeastTwo.{0} Real 250
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 248)))

noncomputable def p19117 :=
p19116
  (@Inv.inv.{0} Real
    (@InvOneClass.toInv.{0} Real
      (@DivInvOneMonoid.toInvOneClass.{0} Real
        (@DivisionMonoid.toDivInvOneMonoid.{0} Real
          (@GroupWithZero.toDivisionMonoid.{0} Real
            (@DivisionSemiring.toGroupWithZero.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))))))
    p18958)

noncomputable def p19118 :=
@Mathlib.Meta.NormNum.isNNRat_mul.{0} Real
  (@DivisionSemiring.toSemiring.{0} Real
    (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real (@Distrib.toMul.{0} Real (@instDistribOfSemiring.{0} Real Real.semiring))))
  (@OfNat.ofNat.{0} Real 250
    (@instOfNatAtLeastTwo.{0} Real 250
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 248)))

noncomputable def p19119 :=
@p19118
  (@Inv.inv.{0} Real
    (@InvOneClass.toInv.{0} Real
      (@DivInvOneMonoid.toInvOneClass.{0} Real
        (@DivisionMonoid.toDivInvOneMonoid.{0} Real
          (@GroupWithZero.toDivisionMonoid.{0} Real
            (@DivisionSemiring.toGroupWithZero.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))))))
    p18958)

noncomputable def p19120 :=
@Mathlib.Meta.NormNum.IsNat.to_isNNRat.{0} Real
  (@DivisionSemiring.toSemiring.{0} Real
    (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))
  (@OfNat.ofNat.{0} Real 250
    (@instOfNatAtLeastTwo.{0} Real 250
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 248)))

noncomputable def p19121 :=
@p19119 250 1 1 1 250 1 250
  (@Eq.refl.{1} (Real → Real → Real)
    (@HMul.hMul.{0, 0, 0} Real Real Real
      (@instHMul.{0} Real (@Distrib.toMul.{0} Real (@instDistribOfSemiring.{0} Real Real.semiring)))))
  (@p19120 250
    (@p19020 250
      (@Eq.refl.{1} Real
        (@OfNat.ofNat.{0} Real 250
          (@instOfNatAtLeastTwo.{0} Real 250
            (@AddMonoidWithOne.toNatCast.{0} Real
              (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 248))))))

noncomputable def p19122 :=
@Mathlib.Meta.NormNum.IsNNRat.to_isNat.{0} Real
  (@DivisionSemiring.toSemiring.{0} Real
    (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))
  (p19112 p18958) 1
  (@p19114 p18958 1 1
    (@Mathlib.Meta.NormNum.IsNat.to_isNNRat.{0} Real
      (@DivisionSemiring.toSemiring.{0} Real
        (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))
      p19115 1
      (@Mathlib.Meta.NormNum.IsNNRat.to_isNat.{0} Real
        (@DivisionSemiring.toSemiring.{0} Real
          (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))
        p19117 1
        (p19121 p18969 (@Eq.refl.{1} Nat (Nat.mul 250 1))
          (@Eq.refl.{1} Nat 250)))))

noncomputable def p19123 :=
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
  (@OfNat.ofNat.{0} Real 250
    (@instOfNatAtLeastTwo.{0} Real 250
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 248)))

noncomputable def p19124 :=
@Mathlib.Meta.NormNum.isNat_eq_true.{0} Real
  (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
  p19123
  (@OfNat.ofNat.{0} Real 250
    (@instOfNatAtLeastTwo.{0} Real 250
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 248)))

noncomputable def p19125 :=
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
  (@OfNat.ofNat.{0} Real 250
    (@instOfNatAtLeastTwo.{0} Real 250
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 248)))

noncomputable def p19126 :=
@p19125 1 250 250
  (@Eq.refl.{1} (Real → Real → Real)
    (@HMul.hMul.{0, 0, 0} Real Real Real
      (@instHMul.{0} Real (@Distrib.toMul.{0} Real (@instDistribOfSemiring.{0} Real Real.semiring)))))
  (p3747
    (@Nat.cast_one.{0} Real
      (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))))
  (@p19020 250
    (@Eq.refl.{1} Real
      (@OfNat.ofNat.{0} Real 250
        (@instOfNatAtLeastTwo.{0} Real 250
          (@AddMonoidWithOne.toNatCast.{0} Real
            (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
          (Mathlib.Meta.NormNum.instAtLeastTwo 248)))))
  (@Eq.refl.{1} Nat 250)

noncomputable def p19127 :=
@p19110 p18957 p18958 p18974
  (@rfl.{1} Real p19111)
  (p19113 p19122
    (p3747
      (@Nat.cast_one.{0} Real
        (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))))
  (@p19124 250 p19126
    (@p19020 250
      (@Eq.refl.{1} Real
        (@OfNat.ofNat.{0} Real 250
          (@instOfNatAtLeastTwo.{0} Real 250
            (@AddMonoidWithOne.toNatCast.{0} Real
              (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 248))))))

noncomputable def p19128 :=
@Mathlib.Tactic.CancelDenoms.mul_subst.{0} Real (@Field.toCommRing.{0} Real Real.instField)
  (@OfNat.ofNat.{0} Real 1
    (@One.toOfNat1.{0} Real
      (@AddMonoidWithOne.toOne.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))))
  (@OfNat.ofNat.{0} Real 250
    (@instOfNatAtLeastTwo.{0} Real 250
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 248)))

noncomputable def p19129 :=
@p19128
  (@OfNat.ofNat.{0} Real 250
    (@instOfNatAtLeastTwo.{0} Real 250
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 248)))

noncomputable def p19130 :=
@p19129
  (@OfNat.ofNat.{0} Real 32
    (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
  Real.pi p3705 (p18975 Real.pi)

noncomputable def p19131 :=
@HMul.hMul.{0, 0, 0} Real Real Real
  (@instHMul.{0} Real
    (@inferInstance.{1} (Mul.{0} Real)
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real
          (@DivisionSemiring.toSemiring.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))))))
  (@OfNat.ofNat.{0} Real 250
    (@instOfNatAtLeastTwo.{0} Real 250
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 248)))

noncomputable def p19132 :=
p19130 (@rfl.{1} Real p3930) (@rfl.{1} Real (p19131 Real.pi))
  (@p19124 250 p19126
    (@p19020 250
      (@Eq.refl.{1} Real
        (@OfNat.ofNat.{0} Real 250
          (@instOfNatAtLeastTwo.{0} Real 250
            (@AddMonoidWithOne.toNatCast.{0} Real
              (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 248))))))

noncomputable def p19133 :=
@Eq.mp.{0}
  (@LT.lt.{0} Real (@Preorder.toLT.{0} Real (@PartialOrder.toPreorder.{0} Real Real.partialOrder))
    p19098
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))))))
  (@LT.lt.{0} Real (@Preorder.toLT.{0} Real (@PartialOrder.toPreorder.{0} Real Real.partialOrder))
    p18976
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))))))
  (@congrArg.{1, 1} Real Prop p19098 p18976
    (fun (_a : Real) =>
      @LT.lt.{0} Real (@Preorder.toLT.{0} Real (@PartialOrder.toPreorder.{0} Real Real.partialOrder)) _a
        (@OfNat.ofNat.{0} Real 0
          (@Zero.toOfNat0.{0} Real
            (@MulZeroClass.toZero.{0} Real
              (@instMulZeroClassOfSemiring.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))))))
    (@p19101 p18976 p19104
      (p19108 p19127 p19132)))

noncomputable def p19134 :=
@Mathlib.Tactic.Linarith.mul_neg.{0} Real Real.instRing Real.partialOrder Real.instIsStrictOrderedRing
  (p19097
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 32
        (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
      Real.pi))

noncomputable def p19135 :=
@Mathlib.Tactic.Linarith.sub_neg_of_lt.{0} Real Real.instRing Real.partialOrder Real.instIsOrderedRing
  (@HDiv.hDiv.{0, 0, 0} Real Real Real
    (@instHDiv.{0} Real
      (@DivInvMonoid.toDiv.{0} Real
        (@GroupWithZero.toDivInvMonoid.{0} Real
          (@DivisionSemiring.toGroupWithZero.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p18957 p18958)

noncomputable def p19136 :=
@Mathlib.Meta.NormNum.isNat_lt_true.{0} Real Real.semiring Real.partialOrder Real.instIsOrderedRing
  (@FloorSemiring.instCharZero.{0} Real (@Ring.toSemiring.{0} Real Real.instRing) Real.partialOrder
    (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing))
  (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
  (@OfNat.ofNat.{0} Real 250
    (@instOfNatAtLeastTwo.{0} Real 250 Real.instNatCast
      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 249 (instOfNatNat 249))
        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 248 (instOfNatNat 248))))))
  0 250
  (@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
    (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
    (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) 0
    (@Nat.cast_zero.{0} Real
      (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))))

noncomputable def p19137 :=
p19136
  (@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
    (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
    (@OfNat.ofNat.{0} Real 250
      (@instOfNatAtLeastTwo.{0} Real 250 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 249 (instOfNatNat 249))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 248 (instOfNatNat 248))))))
    250
    (@Eq.refl.{1} Real
      (@OfNat.ofNat.{0} Real 250
        (@instOfNatAtLeastTwo.{0} Real 250
          (@AddMonoidWithOne.toNatCast.{0} Real
            (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
          (Mathlib.Meta.NormNum.instAtLeastTwo 248)))))

noncomputable def p19138 :=
@Mathlib.Meta.NormNum.isNat_lt_true.{0} Real Real.semiring Real.partialOrder Real.instIsOrderedRing
  (@FloorSemiring.instCharZero.{0} Real (@Ring.toSemiring.{0} Real Real.instRing) Real.partialOrder
    (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing))
  (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
  (@OfNat.ofNat.{0} Real 400
    (@instOfNatAtLeastTwo.{0} Real 400 Real.instNatCast
      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 399 (instOfNatNat 399))
        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 398 (instOfNatNat 398))))))
  0 400
  (@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
    (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
    (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) 0
    (@Nat.cast_zero.{0} Real
      (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))))

noncomputable def p19139 :=
p19138
  (@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
    (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
    (@OfNat.ofNat.{0} Real 400
      (@instOfNatAtLeastTwo.{0} Real 400 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 399 (instOfNatNat 399))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 398 (instOfNatNat 398))))))
    400
    (@Eq.refl.{1} Real
      (@OfNat.ofNat.{0} Real 400
        (@instOfNatAtLeastTwo.{0} Real 400
          (@AddMonoidWithOne.toNatCast.{0} Real
            (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
          (Mathlib.Meta.NormNum.instAtLeastTwo 398)))))

noncomputable def p19140 :=
fun
    (a :
      p18972
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real 32
            (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
          Real.pi)) =>
  @Mathlib.Tactic.Linarith.lt_irrefl.{0} Real Real.instPreorder
    (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
    (p18979 p19090
      (@Mathlib.Tactic.Linarith.add_neg.{0} Real Real.semiring Real.partialOrder Real.instIsStrictOrderedRing
        p19091
        (@HMul.hMul.{0, 0, 0} Real Real Real
          (@instHMul.{0} Real
            (@Distrib.toMul.{0} Real (@instDistribOfSemiring.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))))
          (@OfNat.ofNat.{0} Real 400
            (@instOfNatAtLeastTwo.{0} Real 400 Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 399 (instOfNatNat 399))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 398 (instOfNatNat 398))))))
          p3713)
        (p19092 (p19093 (p19095 (@Eq.refl.{1} Bool false)))
          (p19133
            (@p19134
              (@OfNat.ofNat.{0} Real 250
                (@instOfNatAtLeastTwo.{0} Real 250 Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 249 (instOfNatNat 249))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 248 (instOfNatNat 248))))))
              (@p19135
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real 32
                    (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
                  Real.pi)
                a)
              (p19137 (@Eq.refl.{1} Bool false)))))
        (@Mathlib.Tactic.Linarith.mul_neg.{0} Real Real.instRing Real.partialOrder Real.instIsStrictOrderedRing
          p3713
          (@OfNat.ofNat.{0} Real 400
            (@instOfNatAtLeastTwo.{0} Real 400 Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 399 (instOfNatNat 399))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 398 (instOfNatNat 398))))))
          p3995 (p19139 (@Eq.refl.{1} Bool false)))))

noncomputable def p19141 :=
@Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal d50)
  (hardyZApproximantRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
      true 5))
  false p17677 p15591

noncomputable def p19142 :=
@Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.fstVal d50) p17677
  p15591 p17679 p17680
  (@p19141 p17679 p17680
    (@Eq.refl.{1} Real
      (hardyZApproximantRS
        (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
          true 5)))
    d236)

noncomputable def p19143 :=
@Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal d50)
  (hardyZApproximantRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
      true 5))
  true p18274 p18275

noncomputable def p19144 :=
@Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.sndVal d50) p18274
  p18275 p18277 p18278
  (@p19143 p18277 p18278
    (@Eq.refl.{1} Real
      (hardyZApproximantRS
        (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
          true 5)))
    d245)

noncomputable def p19145 :=
@Zeta.Certificates.ZIntervalRS.Certificate.mk d50
  (@Eq.mpr.{0} p18956 p18959
    (@id.{0} (@Eq.{1} Prop p18956 p18959)
      (@Eq.trans.{1} Prop p18956 p18959 p18959
        (p18961 (p18962 (@Eq.refl.{1} Real p18958)))
        (p18965 (p18970 (@Eq.refl.{1} Real p18958)))))
    (p18971 p19140))
  (BSN.mul_neg_of_pos_neg_r (Zeta.Certificates.ZIntervalRS.fstVal d50)
    (Zeta.Certificates.ZIntervalRS.sndVal d50)
    (p19142 (Eq.refl true) (Eq.refl true) (Eq.refl true))
    (p19144 (Eq.refl true) (Eq.refl true)
      (Eq.refl true)))

noncomputable def p19146 :=
@Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal d50)
  (hardyZErrorBoundRS (@Prod.fst.{0, 0} Real Real (@NonemptyInterval.toProd.{0} Real Real.instLE d50)))
  false false p17677 p15591 p17679

noncomputable def p19147 :=
@p19146 p17680 5945642289 549755813888 201
  549755813888
  (@p19141 p17679 p17680
    (@Eq.refl.{1} Real
      (hardyZApproximantRS
        (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
          true 5)))
    d236)

noncomputable def p19148 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZErrorBoundRS (@Prod.fst.{0, 0} Real Real (@NonemptyInterval.toProd.{0} Real Real.instLE d50)))
  (hardyZErrorBoundRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
      true 5))
  false 5945642289 549755813888

noncomputable def p19149 :=
p19147
  (@p19148 201 549755813888
    (@Eq.refl.{1} Real
      (hardyZErrorBoundRS
        (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779600
          true 5)))
    d246)

noncomputable def p19150 :=
@Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal d50)
  (hardyZErrorBoundRS (@Prod.snd.{0, 0} Real Real (@NonemptyInterval.toProd.{0} Real Real.instLE d50)))
  true false p18274 p18275 p18277

noncomputable def p19151 :=
@p19150 p18278 5936658289 549755813888 201
  549755813888
  (@p19143 p18277 p18278
    (@Eq.refl.{1} Real
      (hardyZApproximantRS
        (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
          true 5)))
    d245)

noncomputable def p19152 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZErrorBoundRS (@Prod.snd.{0, 0} Real Real (@NonemptyInterval.toProd.{0} Real Real.instLE d50)))
  (hardyZErrorBoundRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
      true 5))
  false 5936658289 549755813888

noncomputable def p19153 :=
p19151
  (@p19152 201 549755813888
    (@Eq.refl.{1} Real
      (hardyZErrorBoundRS
        (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101902800
          true 5)))
    d247)

theorem d248 : Zeta.Certificates.ZIntervalRS.Certificate d50 :=
p19145
  (p19149 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (p19153 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
end RHHeight1000.GramZero662

theorem solution : ∃ t ∈ Set.Ioo (1017.79600 : ℝ) (1019.02800 : ℝ), riemannZeta (1 / 2 + Complex.I * t) = 0 := by
  exact riemannZeta.exists_zero_of_zIntervalRS_certificate _ RHHeight1000.GramZero662.d248
