-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.CoefficientPositivity.fz_zero_of_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:37:05.048505+00:00
-- url     : https://prove2.me/submissions/ddaa8849-e795-4ca6-860a-4d8ff910d7bb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LatticeMinorExistence
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExponentialGrowthExclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HolomorphicPeriodicityExtension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_M3bNormHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BoundedSectionAlgebra
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CoefficientPositivity
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_CoefficientPositivity_flow_eq_Zb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_BoundedSectionAlgebra_nfac_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_BoundedSectionAlgebra_pnorm_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_Zb_Zb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_Zb_dom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_nfac_Zb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_ExponentialGrowthExclusion_exists_fd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_ExponentialGrowthExclusion_integral_swap_of_bdd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_LatticeMinorExistence_herm_comb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_LatticeMinorExistence_herm_of_LZ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_LatticeMinorExistence_herm_rank1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.CoefficientPositivity
open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.LatticeMinorExistence
  ReciprocityTheory.ChartRestriction.G.FD.ExponentialGrowthExclusion
open scoped ComplexConjugate ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.FD.CoefficientPositivity
theorem _root_.solution (X : Data E r) (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (g : ℕ) (χ : X.Ψ → Fin 2 → Fin 2 → ℂ) (hcond : IsHermFam χ ∧ X.IsFreqZ g χ)
    (hωex : ∃ ω, X.IsLZBasis g ω) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hPc : ContinuousOn P X.dom)
    (C : ℝ) (hC : ∀ y ∈ X.dom, X.pnorm la P y ≤ C) (ξ : Fin r → E) (hξ : herm X.Gm ξ ξ = 0)
    (a : X.Ψ → Fin 2 → ℂ) (hemb : ∀ τ : X.Ψ, Data.emb τ.1 ξ = X.uvec u a τ)
    (hcusp : ∀ y ∈ X.dom, X.fj la ξ 0 P y = 0) {x0 : Frame X.Ψ r} (hx0 : x0 ∈ X.dom)
    (hinv : ∀ s : X.Ψ → ℝ, X.fz u g χ P (X.flow ξ (fun τ => (s τ : ℂ)) x0) = X.fz u g χ P x0) :
    X.fz u g χ P x0 = 0 := by
  classical
  obtain ⟨-, -, hfd_pos, hfd_top⟩ := (exists_fd X la).choose_spec
  have hωH : ∀ j, IsHermFam (hωex.choose j) := fun j => herm_of_LZ (X := X) (hωex.choose_spec.1 j)
  let K : Set (Fin (4 * Fintype.card X.Ψ) → ℝ) := Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1
  let B : (Fin (4 * Fintype.card X.Ψ) → ℝ) → X.Ψ → Fin 2 → Fin 2 → ℂ :=
    fun t => ∑ j, (t j : ℂ) • hωex.choose j
  let R : (X.Ψ → ℝ) → X.Ψ → Fin 2 → Fin 2 → ℂ := fun s τ i k => (s τ : ℂ) * a τ i * conj (a τ k)
  let e : (Fin (4 * Fintype.card X.Ψ) → ℝ) → ℂ := fun t => cexp (-(4 * Real.pi * I) * X.pairR χ (B t))
  have hfz : ∀ y, X.fz u g χ P y = ∫ t in K, P (X.Zb u (B t) y) * e t := by
    intro y
    simp only [Data.fz, if_pos hcond, dif_pos hωex]
    rfl
  have hHerm : ∀ s t, IsHermFam (B t + R s) := by
    intro s t τ i k
    have h1 := herm_comb (X := X) hωH t τ i k
    have h2 := herm_rank1 X s a τ i k
    simp only at h2
    show (B t + R s) τ k i = conj ((B t + R s) τ i k)
    simp only [Pi.add_apply, B, R, map_add, h1, h2]
  have hdom : ∀ s t, X.Zb u (B t + R s) x0 ∈ X.dom := fun s t => X.Zb_dom u hu _ (hHerm s t) hx0
  have hN0 := BoundedSectionAlgebra.nfac_pos (X := X) hx0 la
  have hbdP : ∀ s t, ‖P (X.Zb u (B t + R s) x0)‖ ≤ C / X.nfac la x0 := by
    intro s t
    have h1 := hC _ (hdom s t)
    rw [BoundedSectionAlgebra.pnorm_eq (X := X), X.nfac_Zb u hu _ (hHerm s t) la x0] at h1
    rw [le_div_iff₀ hN0]
    exact h1
  have he1 : ∀ t, ‖e t‖ = 1 := by
    intro t
    simp only [e]
    rw [show -(4 * (Real.pi : ℂ) * I) * (X.pairR χ (B t) : ℂ) =
      ((-(4 * Real.pi * X.pairR χ (B t)) : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hZc : Continuous fun b : X.Ψ → Fin 2 → Fin 2 → ℂ => X.Zb u b x0 := by
    refine continuous_pi fun τ => continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Data.Zb, Data.zmat, mat, Matrix.mul_apply, Matrix.of_apply]
    fun_prop
  have hBc : Continuous B := by
    simp only [B]
    fun_prop
  have hRc : Continuous R := by
    simp only [R]
    fun_prop
  have hec : Continuous e := by
    simp only [e, B, Data.pairR]
    fun_prop
  let f : (X.Ψ → ℝ) → (Fin (4 * Fintype.card X.Ψ) → ℝ) → ℂ := fun s t => P (X.Zb u (B t + R s) x0) * e t
  have hfc : Continuous (Function.uncurry f) := by
    have h1 : Continuous fun p : (X.Ψ → ℝ) × (Fin (4 * Fintype.card X.Ψ) → ℝ) =>
        P (X.Zb u (B p.2 + R p.1) x0) :=
      hPc.comp_continuous (hZc.comp ((hBc.comp continuous_snd).add (hRc.comp continuous_fst)))
        (fun p => hdom p.1 p.2)
    exact h1.mul (hec.comp continuous_snd)
  have hfb : ∀ s t, ‖f s t‖ ≤ C / X.nfac la x0 := fun s t => by
    simp only [f]
    rw [norm_mul, he1, mul_one]
    exact hbdP s t
  have hK : volume K < ⊤ := (isCompact_univ_pi fun _ => isCompact_Icc).measure_lt_top
  have hswap := integral_swap_of_bdd hfd_top hK hfc hfb

  have hL : ∫ s in (exists_fd X la).choose, ∫ t in K, f s t =
      (volume (exists_fd X la).choose).toReal • X.fz u g χ P x0 := by
    rw [← MeasureTheory.measureReal_def, ← MeasureTheory.setIntegral_const]
    congr 1
    funext s
    rw [← hinv s, hfz, flow_eq_Zb X u ξ a hemb s x0]
    simp only [f, R, X.Zb_Zb u hu]

  have hR0 : ∀ t, ∫ s in (exists_fd X la).choose, f s t = 0 := by
    intro t
    have hy := X.Zb_dom u hu (B t) (herm_comb (X := X) hωH t) hx0
    have hc := hcusp _ hy
    simp only [Data.fj] at hc
    rw [if_pos (fun p _ => ⟨0, by simp⟩), dif_pos (exists_fd X la)] at hc
    simp only [Pi.zero_apply, Complex.ofReal_zero, zero_mul, Finset.sum_const_zero, mul_zero,
      Complex.exp_zero, mul_one] at hc
    have hV : ((volume (exists_fd X la).choose).toReal : ℂ)⁻¹ ≠ 0 :=
      inv_ne_zero (by exact_mod_cast (ENNReal.toReal_pos hfd_pos.ne' hfd_top.ne).ne')
    have hI := (mul_eq_zero.1 hc).resolve_left hV
    have hpt : ∀ s : X.Ψ → ℝ, P (X.Zb u (B t + R s) x0) =
        P (X.flow ξ (fun τ => (s τ : ℂ)) (X.Zb u (B t) x0)) := by
      intro s
      rw [flow_eq_Zb X u ξ a hemb s, X.Zb_Zb u hu, add_comm]
    simp only [f]
    rw [MeasureTheory.integral_mul_const]
    simp_rw [hpt]
    rw [hI, zero_mul]
  rw [hswap] at hL
  simp only [hR0, MeasureTheory.integral_zero] at hL
  have hV : (volume (exists_fd X la).choose).toReal ≠ 0 := (ENNReal.toReal_pos hfd_pos.ne' hfd_top.ne).ne'
  exact (smul_eq_zero.1 hL.symm).resolve_left hV
end ReciprocityTheory.ChartRestriction.G.FD.CoefficientPositivity
