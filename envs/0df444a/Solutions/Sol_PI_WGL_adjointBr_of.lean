-- Prove2me | solution 1 for PI.WGL.adjointBr_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:16:49.495627+00:00
-- url     : https://prove2.me/submissions/9156abe2-13b7-494a-8ebc-e4650d9cd9c2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
import Definitions.Def_Formalism_PeriodIntegrals_HwIrred
import Definitions.Def_Formalism_PeriodIntegrals_SchurFock
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_AdjBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_SqActMemNabla
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ConstructionAdj
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_P2M_PI_WGL_Adj_nf_sqAct_adj__7005aae57fcc
import Theorems.Thm_PI_GTS_re_normFock_smul
import Theorems.Thm_PI_WGL_Adj_cU_zpow_val
import Theorems.Thm_PI_WGL_Adj_embGL_gStar
import Theorems.Thm_PI_WGL_Adj_exists_frame
import Theorems.Thm_PI_WGL_Adj_extremal_mem
import Theorems.Thm_PI_WGL_Adj_extremal_ne
import Theorems.Thm_PI_WGL_Adj_lastGL_cU
import Theorems.Thm_PI_WGL_Adj_nfL_apply
import Theorems.Thm_PI_WGL_Adj_nf_cauchy_schwarz
import Theorems.Thm_PI_WGL_Adj_nf_extremal
import Theorems.Thm_PI_WGL_Adj_nf_self_eq_re
import Theorems.Thm_PI_WGL_Adj_nf_sub_right
import Theorems.Thm_PI_WGL_Adj_nf_sum_smul_left
import Theorems.Thm_PI_WGL_Adj_nf_sum_smul_right
import Theorems.Thm_PI_WGL_Adj_sqAct_mem_nabla
import Theorems.Thm_PI_WGL_Adj_sqAct_smul
import Theorems.Thm_PI_WHw_bC_fd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WGL
open Formalism.BasicNotions MvPolynomial PI.WGL.Adj
namespace PI.WGL
theorem _root_.solution (h3 : PI.HwIrred) (h5 : PI.SchurFock) (hN : Numbers) (hX : XiFacts) :
    AdjointBr := by
  intro n N h lam sg hI io hio hext hlast
  obtain ⟨hioV, hioEq⟩ := hio
  obtain ⟨hc0, hcB, -⟩ := hN n N h lam sg hI
  obtain ⟨hxi0, hxiV, -, -, -, hxiU⟩ := hX n N h lam sg hI
  obtain ⟨d, b, hbV, hexp⟩ := exists_frame n sg
  have hdel_sg : delSq ℂ n sg = nablaSq ℂ n sg := ((h3 n sg).1).symm
  have hdel_lam : delSq ℂ N lam = nablaSq ℂ N lam := ((h3 N lam).1).symm

  let br : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ :=
    ∑ k, (nfL lam (io (b k))).smulRight (b k)
  have hbr : ∀ f, br f = ∑ k, normFock lam f (io (b k)) • b k := by
    intro f
    simp [br, LinearMap.sum_apply, LinearMap.smulRight_apply, nfL_apply]
  have hbrV : ∀ f, br f ∈ nablaSq ℂ n sg := by
    intro f
    rw [hbr]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hbV k)
  have hT : ∀ s ∈ nablaSq ℂ n sg, ∀ f, normFock lam (io s) f = normFock sg s (br f) := by
    intro s hs f
    have e := hexp s hs
    calc normFock lam (io s) f = normFock lam (io (∑ k, normFock sg s (b k) • b k)) f := by rw [← e]
      _ = ∑ k, normFock sg s (b k) * normFock lam (io (b k)) f := by
          rw [map_sum]
          simp only [map_smul]
          rw [nf_sum_smul_left]
      _ = normFock sg s (br f) := by
          rw [hbr, nf_sum_smul_right]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [← nf_herm, mul_comm]
  have hsep : ∀ x y, x ∈ nablaSq ℂ n sg → y ∈ nablaSq ℂ n sg →
      (∀ s ∈ nablaSq ℂ n sg, normFock sg s x = normFock sg s y) → x = y := by
    intro x y hx hy hxy
    have hd : x - y ∈ nablaSq ℂ n sg := Submodule.sub_mem _ hx hy
    have h0 : normFock sg (x - y) (x - y) = 0 := by rw [nf_sub_right, hxy _ hd, sub_self]
    exact sub_eq_zero.mp (nf_self_eq_zero sg _ h0)

  have hB4 : ∀ (g : GL (Fin n) ℂ) (f : MvPolynomial (Fin N × Fin N) ℂ),
      br (sqAct ℂ N lam (embGL ℂ n N h g) f) = sqAct ℂ n sg g (br f) := by
    intro g f
    refine hsep _ _ (hbrV _) (sqAct_mem_nabla sg g _ (hbrV f)) fun s hs => ?_
    have hs' : sqAct ℂ n sg (gStar g) s ∈ nablaSq ℂ n sg := sqAct_mem_nabla sg _ s hs
    rw [← hT s hs, nf_sqAct_adj' lam (embGL ℂ n N h g) (io s) f, ← embGL_gStar, ← hioEq _ s hs,
      hT _ hs', nf_sqAct_adj' sg g s (br f)]
  have hB5 : ∀ (a : ℂˣ) (f : MvPolynomial (Fin N × Fin N) ℂ),
      br (sqAct ℂ N lam (lastGL ℂ N a) f) = ((a ^ degZ lam sg : ℂˣ) : ℂ) • br f := by
    intro a f
    refine hsep _ _ (hbrV _) (Submodule.smul_mem _ _ (hbrV f)) fun s hs => ?_
    rw [← hT s hs, nf_sqAct_adj' lam (lastGL ℂ N a) (io s) f, ← lastGL_cU, hlast _ s hs, nf_smul_left,
      nf_smul_right, hT s hs, cU_zpow_val]

  have hextV : extremal ℂ n sg ∈ nablaSq ℂ n sg := extremal_mem sg
  have hext0 : extremal ℂ n sg ≠ 0 := extremal_ne sg
  let Tm : Module.End ℂ (nablaSq ℂ n sg) :=
    LinearMap.codRestrict (nablaSq ℂ n sg) ((br ∘ₗ io) ∘ₗ (nablaSq ℂ n sg).subtype) (fun x => hbrV _)
  haveI : FiniteDimensional ℂ (nablaSq ℂ n sg) := PI.WHw.bC_fd n n sg.natW
  haveI : Nontrivial (nablaSq ℂ n sg) :=
    ⟨⟨⟨_, hextV⟩, 0, fun h0 => hext0 (congrArg Subtype.val h0)⟩⟩
  obtain ⟨κ, hκ⟩ := Module.End.exists_eigenvalue Tm
  obtain ⟨v, hv⟩ := hκ.exists_hasEigenvector
  have hv1 : br (io (v : MvPolynomial (Fin n × Fin n) ℂ)) = κ • (v : MvPolynomial (Fin n × Fin n) ℂ) := by
    have := Module.End.HasEigenvector.apply_eq_smul hv
    exact congrArg Subtype.val this
  have hv0 : (v : MvPolynomial (Fin n × Fin n) ℂ) ≠ 0 := fun h0 => hv.2 (Subtype.ext h0)
  let U : Submodule ℂ (MvPolynomial (Fin n × Fin n) ℂ) :=
    nablaSq ℂ n sg ⊓ LinearMap.ker (br ∘ₗ io - κ • LinearMap.id)
  have hmemU : ∀ x, x ∈ U ↔ x ∈ nablaSq ℂ n sg ∧ br (io x) = κ • x := by
    intro x
    simp only [U, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  have hUst : ∀ (g : GL (Fin n) ℂ), ∀ x ∈ U, sqAct ℂ n sg g x ∈ U := by
    intro g x hx
    rw [hmemU] at hx ⊢
    refine ⟨sqAct_mem_nabla sg g x hx.1, ?_⟩
    rw [hioEq g x hx.1, hB4, hx.2, sqAct_smul]
  have hall : ∀ s ∈ nablaSq ℂ n sg, br (io s) = κ • s := by
    rcases (h3 n sg).2.1 U inf_le_left hUst with hU | hU
    · exfalso
      have hvU : (v : MvPolynomial (Fin n × Fin n) ℂ) ∈ U := (hmemU _).2 ⟨v.2, hv1⟩
      rw [hU, Submodule.mem_bot] at hvU
      exact hv0 hvU
    · intro s hs
      rw [← hU] at hs
      exact ((hmemU s).1 hs).2

  set K := normFock lam (io (extremal ℂ n sg)) (io (extremal ℂ n sg)) with hKdef
  have hnorm : ∀ s ∈ nablaSq ℂ n sg, normFock lam (io s) (io s) = K * normFock sg s s := by
    have hK : star κ = K := by
      have := hT _ hextV (io (extremal ℂ n sg))
      rw [hall _ hextV, nf_smul_right, nf_extremal, mul_one] at this
      exact this.symm
    intro s hs
    rw [hT s hs, hall s hs, nf_smul_right, hK]
  have hKre : K.re = ‖((cBr h lam sg : ℤ) : ℂ)‖ ^ 2 * (normFock lam (xi ℂ h lam sg) (xi ℂ h lam sg)).re := by
    rw [hKdef, hext, PI.GTS.re_normFock_smul]
  have hKreal : K = ((K.re : ℝ) : ℂ) := by rw [hKdef]; exact nf_self_eq_re lam _
  have hcpos : 0 < ‖((cBr h lam sg : ℤ) : ℂ)‖ := by
    rw [norm_pos_iff]; exact_mod_cast hc0
  have hKpos : 0 < K.re := by
    rw [hKre]; exact mul_pos (pow_pos hcpos 2) (nf_self_re_pos lam _ hxi0)
  have hKle : K.re ≤ brBd h lam sg ^ 2 := by
    have hc2 : ‖((cBr h lam sg : ℤ) : ℂ)‖ ^ 2 ≤ cBd h lam sg ^ 2 := by
      have hcn : ‖((cBr h lam sg : ℤ) : ℂ)‖ = |((cBr h lam sg : ℤ) : ℝ)| := by
        rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
      rw [hcn]
      exact pow_le_pow_left₀ (abs_nonneg _) hcB 2
    have hSF := h5 N lam (xi ℂ h lam sg) hxiV hxiU
    have hbb : brBd h lam sg ^ 2 = cBd h lam sg ^ 2 * (Module.finrank ℂ (delSq ℂ N lam) : ℝ) := by
      unfold brBd; rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    rw [hKre, hbb]
    exact mul_le_mul hc2 hSF (nf_self_re_nonneg lam _) (sq_nonneg _)
  refine ⟨?_, br, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  ·
    intro s hs
    rw [hnorm s hs, hKreal, Complex.re_ofReal_mul]
    exact mul_le_mul_of_nonneg_right hKle (nf_self_re_nonneg sg s)
  ·
    intro f _
    rw [hdel_sg]; exact hbrV f
  ·
    refine ⟨io (extremal ℂ n sg), ?_, ?_⟩
    · rw [hdel_lam]; exact hioV _ hextV
    · intro h0
      have := hT _ hextV (io (extremal ℂ n sg))
      rw [h0, nf_zero_right] at this
      rw [← hKdef] at this
      rw [this] at hKpos
      simp at hKpos
  ·
    intro g f _
    exact hB4 g f
  ·
    intro a f _
    exact hB5 a f
  ·
    intro f _
    set u := br f with hu
    have huV : u ∈ nablaSq ℂ n sg := hbrV f
    have hTu : normFock lam (io u) f = normFock sg u u := hT u huV f
    have hCS := nf_cauchy_schwarz lam (io u) f
    have hnA : ‖normFock sg u u‖ = (normFock sg u u).re := by
      conv_lhs => rw [nf_self_eq_re sg u]
      exact Complex.norm_of_nonneg (nf_self_re_nonneg sg u)
    rw [nf_herm lam (io u) f, hTu, norm_star, hnA, hnorm u huV, hKreal, Complex.re_ofReal_mul] at hCS
    have hA := nf_self_re_nonneg sg u
    have hF := nf_self_re_nonneg lam f
    have hAle : (normFock sg u u).re ≤ K.re * (normFock lam f f).re := by
      rcases hA.lt_or_eq with hApos | hA0
      · refine le_of_mul_le_mul_left ?_ hApos
        nlinarith
      · rw [← hA0]; exact mul_nonneg hKpos.le hF
    calc (normFock sg u u).re ≤ K.re * (normFock lam f f).re := hAle
      _ ≤ brBd h lam sg ^ 2 * (normFock lam f f).re := mul_le_mul_of_nonneg_right hKle hF
  ·
    intro s hs f _
    exact hT s hs f
end PI.WGL
