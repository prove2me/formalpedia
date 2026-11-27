-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.noShortVectorLowerBound_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:27:55.275287+00:00
-- url     : https://prove2.me/submissions/c3433b99-0be2-4cd9-b009-683fc6c89183

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicCoefficientSplitting
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FinrankRieszBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegerApproximationCountHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_NoShortVectorLowerBoundHolds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_Hf_eq_jp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_hermC_jp_jp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_DiscreteLatticeMinimum_Bmap_Bmap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_DiscreteLatticeMinimum_covering
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_DiscriminantTraceBounds_two_le_normSq_mul_rootDisc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FinrankRieszBounds_finrank_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FinrankRieszBounds_maj_csmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FinrankRieszBounds_riesz
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantOperators_Hf_cs
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantOperators_Hf_sub_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantOperators_conj_purely_imaginary_generator
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantOperators_maj_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_RealTangentSpace_maj_le_norm_sq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_RealTangentSpace_phi_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_UnipotentCoefficientShift_Hf_smul_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_integerApproximationCount_holds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Module RealTangentSpace DiscreteLatticeMinimum
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
namespace ReciprocityTheory.ChartRestriction.G.FD
theorem _root_.solution : NoShortVectorLowerBound (E := E) := by
  intro r X ξ ep0 hξ hep z hz hgap δ
  have hz' : z ∈ X.dom ∧ ∀ τ : X.Ψ, X.c τ * X.maj z τ (Data.emb τ.1 ξ) = 1 := hz
  have hz1 : z ∈ X.dom := hz'.1
  haveI hzf : Fact (z ∈ X.dom) := ⟨hz1⟩
  have hk0 : 0 < X.k0 := X.minWeight_pos
  have hk0ne : X.k0 ≠ 0 := hk0.ne'
  have hdE : 0 < dE E := by
    unfold dE
    exact abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero (K := E)))
  have hdEne : dE E ≠ 0 := hdE.ne'
  have hrd : 0 ≤ rdE E := by
    unfold rdE
    exact Real.rpow_nonneg hdE.le _
  have hepne : ep0 ≠ 0 := hep.ne'
  obtain ⟨d, hd⟩ : ∃ d : VT (X := X.toData) z ξ, ∀ u ∈ X.Uz z ξ, ∀ τ : X.Ψ,
      δ τ (u τ) = X.Hf z τ (u τ) (d.val τ) := by
    apply FinrankRieszBounds.riesz <;> assumption
  obtain ⟨d', hd'⟩ : ∃ d' : VT (X := X.toData) z ξ,
      d' = (2 / (dE E * X.k0 ^ 2)) • Bmap z ξ d := ⟨_, rfl⟩
  obtain ⟨μ, hμ⟩ : ∃ μ : X.Λp ξ, ‖d' - phi z ξ hξ μ‖ ≤
      (finrank ℝ (VT (X := X.toData) z ξ) : ℝ) ^ 3 * X.NA / (2 * X.k0 * Real.sqrt ep0) := by
    apply DiscreteLatticeMinimum.covering (Y := X) (z := z) (ξ := ξ) (hD3 := integerApproximationCount_holds) (hep := hep) <;> assumption
  have hfin : finrank ℝ (VT (X := X.toData) z ξ) ≤ 2 * fdeg E * (r - 2) := by
    apply FinrankRieszBounds.finrank_le <;> assumption
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = finrank ℝ (VT (X := X.toData) z ξ) := ⟨_, rfl⟩
  rw [← hn] at hμ hfin
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = ‖d' - phi z ξ hξ μ‖ := ⟨_, rfl⟩
  rw [← hDdef] at hμ
  obtain ⟨w, hw⟩ : ∃ w : VT (X := X.toData) z ξ,
      w = (-(dE E / 2)) • Bmap z ξ (d' - phi z ξ hξ μ) := ⟨_, rfl⟩
  have hd_eq : (-(dE E / 2)) • Bmap z ξ d' = d := by
    rw [hd', map_smul, DiscreteLatticeMinimum.Bmap_Bmap, smul_smul, smul_smul]
    convert one_smul ℝ d using 2
    field_simp <;> ring
  have hw_eq : w = d - (-(dE E / 2)) • Bmap z ξ (phi z ξ hξ μ) := by
    rw [hw, map_sub, smul_sub, hd_eq]
  have hwn : ‖w‖ = dE E / 2 * (X.k0 * D) := by
    rw [hw, norm_smul, DiscreteLatticeMinimum.norm_Bmap, ← hDdef, Real.norm_eq_abs, abs_neg,
      abs_of_pos (half_pos hdE)]
  have hspos : 0 < Real.sqrt ep0 := Real.sqrt_pos.mpr hep
  have hsq : Real.sqrt ep0 ^ 2 = ep0 := Real.sq_sqrt hep.le
  have hden : 0 < 2 * X.k0 * Real.sqrt ep0 := mul_pos (mul_pos two_pos hk0) hspos
  have hD0 : 0 ≤ D := by rw [hDdef]; exact norm_nonneg _
  have hB : D * (2 * X.k0 * Real.sqrt ep0) ≤ (n : ℝ) ^ 3 * X.NA := (le_div_iff₀ hden).mp hμ
  have hD2 : D ^ 2 * (4 * X.k0 ^ 2 * ep0) ≤ ((n : ℝ) ^ 3 * X.NA) ^ 2 := by
    have h0 : 0 ≤ D * (2 * X.k0 * Real.sqrt ep0) := mul_nonneg hD0 hden.le
    have h1 := pow_le_pow_left₀ h0 hB 2
    have h2 : D ^ 2 * (4 * X.k0 ^ 2 * ep0) = (D * (2 * X.k0 * Real.sqrt ep0)) ^ 2 := by
      linear_combination (-(4 * D ^ 2 * X.k0 ^ 2)) * hsq
    rw [h2]
    exact h1
  have hx : 0 ≤ (X.NC : ℝ) ^ 2 * rdE E / ep0 :=
    div_nonneg (mul_nonneg (sq_nonneg _) hrd) hep.le
  have hM2 : frameIndexBound r (fdeg E) (dE E) (rdE E) X.NA X.NC ep0 ^ 2 =
      (fdeg E : ℝ) ^ 2 * ((2 * fdeg E * (r - 2) : ℕ) : ℝ) ^ 6 * dE E ^ 2 * (X.NA : ℝ) ^ 2 *
        ((X.NC : ℝ) ^ 2 * rdE E / ep0) := by
    have hs := Real.sq_sqrt hx
    rw [frameIndexBound]
    linear_combination ((fdeg E : ℝ) * ((2 * fdeg E * (r - 2) : ℕ) : ℝ) ^ 3 * dE E *
      (X.NA : ℝ)) ^ 2 * hs
  have hwM : ‖w‖ ^ 2 ≤ frameIndexBound r (fdeg E) (dE E) (rdE E) X.NA X.NC ep0 ^ 2 * X.k0 := by
    rw [hwn, hM2]
    have hlhs : (dE E / 2 * (X.k0 * D)) ^ 2 * (16 * ep0) ≤
        dE E ^ 2 * (X.NA : ℝ) ^ 2 * (n : ℝ) ^ 6 := by
      have h3 : (dE E / 2 * (X.k0 * D)) ^ 2 * (16 * ep0) =
          dE E ^ 2 * (D ^ 2 * (4 * X.k0 ^ 2 * ep0)) := by ring
      rw [h3]
      calc dE E ^ 2 * (D ^ 2 * (4 * X.k0 ^ 2 * ep0)) ≤ dE E ^ 2 * (((n : ℝ) ^ 3 * X.NA) ^ 2) :=
            mul_le_mul_of_nonneg_left hD2 (sq_nonneg _)
        _ = dE E ^ 2 * (X.NA : ℝ) ^ 2 * (n : ℝ) ^ 6 := by ring
    have hQ : 0 ≤ dE E ^ 2 * (X.NA : ℝ) ^ 2 := by positivity
    have hS : 0 ≤ (X.NC : ℝ) ^ 2 * X.k0 * rdE E :=
      mul_nonneg (mul_nonneg (sq_nonneg _) hk0.le) hrd
    have hn6 : (n : ℝ) ^ 6 ≤ ((2 * fdeg E * (r - 2) : ℕ) : ℝ) ^ 6 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hfin) 6
    have hinv : ep0 * ep0⁻¹ = 1 := mul_inv_cancel₀ hepne
    have heq : (fdeg E : ℝ) ^ 2 * ((2 * fdeg E * (r - 2) : ℕ) : ℝ) ^ 6 * dE E ^ 2 *
        (X.NA : ℝ) ^ 2 * ((X.NC : ℝ) ^ 2 * rdE E / ep0) * X.k0 * (16 * ep0) =
        16 * ((fdeg E : ℝ) ^ 2 * (dE E ^ 2 * (X.NA : ℝ) ^ 2 *
          ((2 * fdeg E * (r - 2) : ℕ) : ℝ) ^ 6)) * ((X.NC : ℝ) ^ 2 * X.k0 * rdE E) := by
      linear_combination (16 * (fdeg E : ℝ) ^ 2 * ((2 * fdeg E * (r - 2) : ℕ) : ℝ) ^ 6 *
        dE E ^ 2 * (X.NA : ℝ) ^ 2 * (X.NC : ℝ) ^ 2 * rdE E * X.k0) * hinv
    have hP : 0 ≤ dE E ^ 2 * (X.NA : ℝ) ^ 2 * ((2 * fdeg E * (r - 2) : ℕ) : ℝ) ^ 6 := by
      positivity
    have h6 : dE E ^ 2 * (X.NA : ℝ) ^ 2 * (n : ℝ) ^ 6 ≤
        dE E ^ 2 * (X.NA : ℝ) ^ 2 * ((2 * fdeg E * (r - 2) : ℕ) : ℝ) ^ 6 :=
      mul_le_mul_of_nonneg_left hn6 hQ
    have hrhs : dE E ^ 2 * (X.NA : ℝ) ^ 2 * (n : ℝ) ^ 6 ≤
        16 * ((fdeg E : ℝ) ^ 2 * (dE E ^ 2 * (X.NA : ℝ) ^ 2 *
          ((2 * fdeg E * (r - 2) : ℕ) : ℝ) ^ 6)) * ((X.NC : ℝ) ^ 2 * X.k0 * rdE E) := by
      by_cases hN : ((2 * fdeg E * (r - 2) : ℕ) : ℝ) = 0
      · have hP0 : dE E ^ 2 * (X.NA : ℝ) ^ 2 * ((2 * fdeg E * (r - 2) : ℕ) : ℝ) ^ 6 = 0 := by
          rw [hN]; ring
        have h5 : 0 ≤ 16 * ((fdeg E : ℝ) ^ 2 * (dE E ^ 2 * (X.NA : ℝ) ^ 2 *
            ((2 * fdeg E * (r - 2) : ℕ) : ℝ) ^ 6)) * ((X.NC : ℝ) ^ 2 * X.k0 * rdE E) :=
          mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg _) hP)) hS
        linarith
      · have hN' : 2 * fdeg E * (r - 2) ≠ 0 := by exact_mod_cast hN
        have hf0 : fdeg E ≠ 0 := fun h => hN' (by simp [h])
        have hr : 0 < r := Nat.pos_of_ne_zero (fun h => hN' (by simp [h]))
        have hk : 2 ≤ (X.NC : ℝ) ^ 2 * X.k0 * rdE E := by
          apply DiscriminantTraceBounds.two_le_normSq_mul_rootDisc <;> assumption
        have hf1 : (1 : ℝ) ≤ (fdeg E : ℝ) ^ 2 := by
          have h1 : (1 : ℝ) ≤ fdeg E := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hf0
          nlinarith
        have h7 : 2 ≤ (fdeg E : ℝ) ^ 2 * ((X.NC : ℝ) ^ 2 * X.k0 * rdE E) := by nlinarith
        have h8 := mul_le_mul_of_nonneg_left h7 hP
        linarith
    exact le_of_mul_le_mul_right (hlhs.trans (hrhs.trans_eq heq.symm)) (mul_pos (by norm_num) hep)
  refine ⟨(μ : Fin r → E), μ.2, ?_⟩
  intro u hu τ
  have hsm : ∀ (c : ℝ) (v : Fin r → ℂ),
      X.Hf z τ (u τ) (c • v) = (c : ℂ) * X.Hf z τ (u τ) v := by
    intro c v
    have hcv : c • v = (c : ℂ) • v := (Complex.coe_smul c v).symm
    rw [hcv, UnipotentCoefficientShift.Hf_smul_right, Complex.conj_ofReal]
  have hkey : δ τ (u τ) - (dE E : ℂ) * (-τ.1 X.ξ0) *
      hermC τ.1 X.Gm (u τ) (X.ucomp z ξ (X.embV (μ : Fin r → E)) τ) =
      X.Hf z τ (u τ) (w.val τ) := by
    rw [hw_eq, VT.val_sub, VT.val_smul, Pi.sub_apply, Pi.smul_apply, MajorantOperators.Hf_sub_right,
      ← hd u hu τ, DiscreteLatticeMinimum.Bmap_val, RealTangentSpace.phi_val]
    congr 1
    rw [hsm]
    simp only [MajorantOperators.Bop]
    rw [UnipotentCoefficientShift.Hf_smul_right, Data.Hf_eq_jp, X.hermC_jp_jp hz1]
    simp only [map_mul, map_neg, map_ofNat, MajorantOperators.conj_purely_imaginary_generator]
    push_cast
    ring
  rw [hkey, FinrankRieszBounds.maj_csmul hz1]
  have hc : X.k0 * X.maj z τ (Data.emb τ.1 ξ) = 1 := by
    have h2 := hz'.2 τ
    simp only [Data.c] at h2
    rw [X.ξ0_abs τ] at h2
    linear_combination h2
  have hme : 0 ≤ X.maj z τ (Data.emb τ.1 ξ) := MajorantOperators.maj_nonneg hz1 τ _
  have hmu : 0 ≤ X.maj z τ (u τ) := MajorantOperators.maj_nonneg hz1 τ _
  have hcs := MajorantOperators.Hf_cs hz1 τ (u τ) (w.val τ)
  have hmw : X.maj z τ (w.val τ) ≤ ‖w‖ ^ 2 := by
    apply RealTangentSpace.maj_le_norm_sq
  calc ‖X.Hf z τ (u τ) (w.val τ)‖ ^ 2 * X.maj z τ (Data.emb τ.1 ξ)
      ≤ (X.maj z τ (u τ) * X.maj z τ (w.val τ)) * X.maj z τ (Data.emb τ.1 ξ) :=
        mul_le_mul_of_nonneg_right hcs hme
    _ ≤ (X.maj z τ (u τ) * (frameIndexBound r (fdeg E) (dE E) (rdE E) X.NA X.NC ep0 ^ 2 * X.k0)) *
        X.maj z τ (Data.emb τ.1 ξ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hmw.trans hwM) hmu) hme
    _ = frameIndexBound r (fdeg E) (dE E) (rdE E) X.NA X.NC ep0 ^ 2 * X.maj z τ (u τ) *
        (X.k0 * X.maj z τ (Data.emb τ.1 ξ)) := by ring
    _ = frameIndexBound r (fdeg E) (dE E) (rdE E) X.NA X.NC ep0 ^ 2 * X.maj z τ (u τ) := by
        rw [hc, mul_one]
end ReciprocityTheory.ChartRestriction.G.FD
