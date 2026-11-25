-- Prove2me | solution 1 for PIW.FdPA.fundamentalDomain_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:35:18.767708+00:00
-- url     : https://prove2.me/submissions/de0cb1f4-42fd-42a3-ad9e-7542fb05f67b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_ZnNonneg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_DivLeExpOfAbsLogSubLe
import Theorems.Thm_PIW_FdPA_inv_mul_between_ratio
import Theorems.Thm_PIW_FdPA_div_le_exp_of_abs_log_sub_le
import Theorems.Thm_PIW_FdPA_small_power_bound
import Theorems.Thm_PIW_FdPA_rh_facts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PIW PIW.FdPA
open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex Metric
noncomputable section
namespace PIW.FdPA
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E]
    (hFd : FjDiff E) (hFb : FjBEq E) (hFc : FjBdd E) (hOD : OrthoDom E) (hUD : UnitDom E)
    (hBF : BorFlag E) (hZs : ZnSmul E) (hZn : ZnNonneg E) (hNp : NfacPos E) (hX0 : XZZero E)
    (h0 : OrthonormalFlagTranslate (E := E)) (h1 : OrthonormalChartNormControl (E := E)) (h2 : NearSupremumTransference (E := E))
    (h3 : SchwarzLemmaBall) (h4 : OrthonormalShortVectorBound (E := E)) (h7 : UnitaryUnipotentMove (E := E)) :
    FundamentalDomainPointBound (E := E) := by
  intro r X la P ξ ν c1 w z0 hD hrw
  dsimp only
  intro n' hn'
  obtain ⟨-, hPSS, hIso, hc1, -, -, hw1, hspr, -, hz0D1, hsup⟩ := id hD
  have hBdd : X.IsBddSec la P := hPSS.1
  have hSec : X.IsSec la P := hBdd.1
  have hFdiff : DifferentiableOn ℂ (X.fj la ξ ν P) X.dom := hFd r X.toData la P ξ ν hBdd hIso
  have hFb' : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r,
      X.fj la ξ ν P (rmul x b) = bchar la b * X.fj la ξ ν P x :=
    hFb r X.toData la P ξ ν hSec hIso
  obtain ⟨C, hC⟩ := hFc r X.toData la P ξ ν hBdd hIso
  obtain ⟨hP0a, hP0b, hP0c⟩ := h0 r X.toData
  have hpn_inv := hP0b la (X.fj la ξ ν P) hFb'
  obtain ⟨hz0dom, hz0c⟩ := hz0D1
  have hself : ∀ x, X.SameFlag x x := fun x τ => rfl
  have htrans : ∀ x y z, X.SameFlag x y → X.SameFlag y z → X.SameFlag x z :=
    fun x y z h1 h2 τ => (h1 τ).trans (h2 τ)
  set F := X.fj la ξ ν P with hF
  have hpn_le_hat : ∀ y ∈ X.dom, X.pnorm la F y ≤ X.hatN la F y := by
    intro y hy
    refine le_csSup ⟨C, ?_⟩ ⟨y, hy, hself y, rfl⟩
    rintro _ ⟨x', hx', -, rfl⟩
    exact hC x' hx'
  have hhat_le : ∀ y ∈ X.dom, X.hatN la F y ≤ C := by
    intro y hy
    refine csSup_le ⟨_, y, hy, hself y, rfl⟩ ?_
    rintro _ ⟨x', hx', -, rfl⟩
    exact hC x' hx'
  set S := sSup {t | ∃ y ∈ X.FramesOverBasis ξ, t = X.hatN la F y} with hS
  have hSbdd : BddAbove {t | ∃ y ∈ X.FramesOverBasis ξ, t = X.hatN la F y} :=
    ⟨C, by rintro _ ⟨y, hy, rfl⟩; exact hhat_le y hy.1⟩
  have hz0S : X.hatN la F z0 ≤ S := le_csSup hSbdd ⟨z0, ⟨hz0dom, hz0c⟩, rfl⟩
  have hlt : S / 2 < sSup {t | ∃ x' ∈ X.dom, X.SameFlag z0 x' ∧ t = X.pnorm la F x'} := by
    have h := hsup
    change S < 2 * X.hatN la F z0 at h
    change S / 2 < X.hatN la F z0
    linarith
  obtain ⟨_, ⟨x', hx'dom, hzx', rfl⟩, hx'lt⟩ :=
    exists_lt_of_lt_csSup (⟨_, z0, hz0dom, hself z0, rfl⟩ :
      {t | ∃ x' ∈ X.dom, X.SameFlag z0 x' ∧ t = X.pnorm la F x'}.Nonempty) hlt
  have hx'le : X.pnorm la F x' ≤ S := by
    refine le_trans ?_ hz0S
    refine le_csSup ⟨C, ?_⟩ ⟨x', hx'dom, hzx', rfl⟩
    rintro _ ⟨y, hy, -, rfl⟩
    exact hC y hy
  have hS0 : 0 ≤ S := by
    refine le_trans ?_ hx'le
    exact mul_nonneg (norm_nonneg _) (hNp r X.toData la x' hx'dom).le
  obtain ⟨b, hb, hortho⟩ := hP0a x' hx'dom
  have hx0dom : rmul x' b ∈ X.dom := hOD r X.toData _ hortho
  have hx'x0 : X.SameFlag x' (rmul x' b) := hBF r X.toData x' b hb hx0dom
  have hz0x0 : X.SameFlag z0 (rmul x' b) := htrans _ _ _ hzx' hx'x0
  have hpx0 : X.pnorm la F (rmul x' b) = X.pnorm la F x' := hpn_inv x' hx'dom b hb
  have hmaj : X.maj z0 = X.maj (rmul x' b) := (hP0c z0 hz0dom _ hx0dom hz0x0).2
  set x0 := rmul x' b with hx0
  obtain ⟨hrh0, hrh1, hwrh⟩ := rh_facts (c1 := c1) (w := w) hc1 hw1
  obtain ⟨hP1b, -⟩ := h1 r X.toData x0 hx0dom hortho (d6rh c1 w) hrh0 hrh1.le
  obtain ⟨-, hP1d⟩ := h1 r X.toData x0 hx0dom hortho (1 / 10) (by norm_num) le_rfl
  obtain ⟨lam, h1m, Z1, hU1, hline, hUz, hsplit1, hflag1, hZ1⟩ :=
    h4 r X la P ξ ν c1 w z0 hD x0 hx0dom hortho hz0x0
  obtain ⟨n, Z, hUn, -, hn'p, hsplit, hflag, hZ⟩ :=
    h7 r X la P ξ ν c1 w z0 hD x0 hx0dom hortho hz0x0 lam h1m Z1 hU1 hline hUz hsplit1 hflag1
      hZ1 n' hn'
  set rh := d6rh c1 w with hrh
  have hZn0 : 0 ≤ X.zN Z := hZn r X.toData Z
  have hZle : X.zN Z ≤ rh := by linarith
  obtain ⟨hxdom, -, -⟩ := hP1b Z hZle
  have hx''dom : X.lmulC n (X.lmulC h1m z0) ∈ X.dom :=
    hUD r X.toData n _ hUn (hUD r X.toData h1m z0 hU1 hz0dom)
  obtain ⟨hJ, -, hA⟩ := (hP0c _ hx''dom _ hxdom hflag).1 ξ
  have hucomp : ∀ u, X.ucomp (X.lmulC n (X.lmulC h1m z0)) ξ u = X.ucomp (X.xZ x0 Z) ξ u :=
    fun u => by simp only [Data.ucomp, hA]
  refine ⟨X.xZ x0 Z, hxdom, lam, ?_⟩
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := hsplit
  refine ⟨s1, s2, s3, fun j hj => ?_, fun j hj => ?_, s6, fun μ hμ => ?_, ?_⟩
  · obtain ⟨a1, a2⟩ := s4 j hj
    refine ⟨a1, ?_⟩
    rw [← hJ, ← hucomp]
    exact a2
  · obtain ⟨a1, a2⟩ := s5 j hj
    refine ⟨a1, ?_⟩
    rw [← hJ, ← hucomp]
    exact a2
  · obtain ⟨e, he, he2⟩ := hn'p μ hμ
    exact ⟨e, he, by rw [← hA]; exact he2⟩
  · set s := X.zN Z with hs
    have hmaxpos : 0 < max s (rh / 22) := lt_max_of_lt_right (by positivity)
    set ρ := rh / max s (rh / 22) with hρ
    have hρpos : 0 < ρ := div_pos hrh0 hmaxpos
    have hρs : ρ * s ≤ rh := by
      rw [hρ, div_mul_eq_mul_div, div_le_iff₀ hmaxpos]
      exact mul_le_mul_of_nonneg_left (le_max_left _ _) hrh0.le
    have h21 : 21 < ρ := by
      rw [hρ, lt_div_iff₀ hmaxpos]
      rcases le_total s (rh / 22) with h | h
      · rw [max_eq_right h]
        linarith
      · rw [max_eq_left h]
        linarith
    have hzt : ∀ t : ℂ, ‖t‖ ≤ ρ → X.zN (t • Z) ≤ rh := by
      intro t ht
      rw [hZs r X.toData t Z]
      calc ‖t‖ * s ≤ ρ * s := mul_le_mul_of_nonneg_right ht hZn0
        _ ≤ rh := hρs
    have hx0nf : 0 < X.nfac la x0 := hNp r X.toData la x0 hx0dom
    let γ : ℂ → ℂ := fun t => F (X.xZ x0 (t • Z)) * (X.nfac la x0 : ℂ)
    have hγd : DifferentiableOn ℂ γ (closedBall 0 ρ) := by
      have hG := hP1d F hFdiff
      have hlin : Differentiable ℂ (fun t : ℂ => t • Z) := differentiable_id.smul_const Z
      refine (hG.comp hlin.differentiableOn ?_).mul_const _
      intro t ht
      simp only [Set.mem_setOf_eq]
      have h := hzt t (mem_closedBall_zero_iff.mp ht)
      linarith
    have hγb : ∀ t ∈ closedBall (0 : ℂ) ρ, ‖γ t‖ ≤ Real.exp (9 / 4) * S := by
      intro t ht
      have htb := hzt t (mem_closedBall_zero_iff.mp ht)
      obtain ⟨hydom, hylog, hymaj⟩ := hP1b (t • Z) htb
      have hynf : 0 < X.nfac la (X.xZ x0 (t • Z)) := hNp r X.toData la _ hydom
      have hlog := hylog la w hspr
      have hsm : 4 * w * r * X.zN (t • Z) ^ 2 ≤ 1 / 4 :=
        small_power_bound (by positivity) hrw (by linarith) hrh0.le hwrh (hZn r X.toData _) htb
      have hratio : X.nfac la x0 / X.nfac la (X.xZ x0 (t • Z)) ≤ Real.exp (1 / 4) :=
        div_le_exp_of_abs_log_sub_le hx0nf hynf (by linarith)
      have htt : ∀ τ, (1 - rh) / (1 + rh) ≤ X.tt ξ (X.xZ x0 (t • Z)) τ ∧
          X.tt ξ (X.xZ x0 (t • Z)) τ ≤ (1 + rh) / (1 - rh) := by
        intro τ
        have hcpos : 0 < X.c τ :=
          mul_pos two_pos (norm_pos_iff.mpr ((map_ne_zero _).mpr X.ξ0_ne))
        have hm0 : X.c τ * X.maj x0 τ (Data.emb τ.1 ξ) = 1 := by
          rw [← hmaj]
          exact hz0c τ
        obtain ⟨hlo, hhi⟩ := hymaj τ (Data.emb τ.1 ξ)
        exact inv_mul_between_ratio hrh0 (by linarith) hcpos hm0 hlo hhi
      have hyhat : X.hatN la F (X.xZ x0 (t • Z)) ≤ Real.exp 2 * S :=
        h2 r X la P ξ ν c1 w z0 hD _ hydom htt
      have hpy : X.pnorm la F (X.xZ x0 (t • Z)) =
          ‖F (X.xZ x0 (t • Z))‖ * X.nfac la (X.xZ x0 (t • Z)) := by
        rw [Data.pnorm, Data.nfac]
      have hnorm : ‖γ t‖ = X.pnorm la F (X.xZ x0 (t • Z)) *
          (X.nfac la x0 / X.nfac la (X.xZ x0 (t • Z))) := by
        simp only [γ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0nf, hpy]
        field_simp
      rw [hnorm]
      calc X.pnorm la F (X.xZ x0 (t • Z)) * (X.nfac la x0 / X.nfac la (X.xZ x0 (t • Z)))
          ≤ (Real.exp 2 * S) * Real.exp (1 / 4) :=
            mul_le_mul ((hpn_le_hat _ hydom).trans hyhat) hratio
              (div_nonneg hx0nf.le hynf.le) (mul_nonneg (Real.exp_pos 2).le hS0)
        _ = Real.exp (9 / 4) * S := by
            rw [mul_right_comm, ← Real.exp_add]
            norm_num
    have hγ0 : ‖γ 0‖ = X.pnorm la F x0 := by
      simp only [γ, zero_smul, hX0 r X.toData x0, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hx0nf]
      rw [Data.pnorm, Data.nfac]
    have hP3 := h3 ℂ γ ρ S hρpos hγd hγb (by rw [hγ0, hpx0]; linarith)
      (by rw [hγ0, hpx0]; exact hx'le) 1
      (by rw [mem_ball_zero_iff, norm_one, lt_div_iff₀ (by norm_num)]; linarith)
    intro hF0
    apply hP3
    simp only [γ, one_smul]
    rw [hF0, zero_mul]
end PIW.FdPA
