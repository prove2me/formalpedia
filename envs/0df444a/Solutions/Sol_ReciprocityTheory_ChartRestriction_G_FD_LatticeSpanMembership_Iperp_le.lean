-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.LatticeSpanMembership.Iperp_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:30:29.372912+00:00
-- url     : https://prove2.me/submissions/92787bcc-74b7-44f8-b945-03314a01180f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantOperators
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LatticeSpanMembership
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_LatticeSpanMembership_mem__p_iff_0da98c18e74b
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_LatticeSpanMembership_smul_int_mem
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_LatticeSpanMembership_mem_span___509d2e199990
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_LatticeSpanMembership_scal_closed
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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_herm_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_herm_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_herm_sub_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_emb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_left
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
open ReciprocityTheory.ChartRestriction.G.FD.LatticeSpanMembership
open NumberField Complex Module
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
namespace ReciprocityTheory.ChartRestriction.G.FD.LatticeSpanMembership
theorem _root_.solution (hD3 : IntegerApproximationCount (E := E)) {ξ : Fin r → E} (hξ : X.IsIso ξ)
    {v : X.Ψ → Fin r → ℂ} (hv : v ∈ X.Iperp ξ) :
    v ∈ Submodule.span ℝ (X.embV '' (X.Λp ξ : Set (Fin r → E))) := by
  classical
  obtain ⟨hξΛ, -, hξ0⟩ := hξ
  obtain ⟨η, hηΛ, hηξ⟩ : ∃ η ∈ X.Λ, herm X.Gm η ξ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ v : Fin r → E, herm X.Gm v ξ = 0 := by
      intro v
      have hv : v ∈ Submodule.span E (X.Λ : Set (Fin r → E)) := X.Λ_span ▸ Submodule.mem_top
      induction hv using Submodule.span_induction with
      | mem v hv => exact hcon v hv
      | zero => simp [herm]
      | add v w _ _ ihv ihw => rw [HermitianTraceFormVanishing.herm_add_left, ihv, ihw, add_zero]
      | smul c v _ ihv => rw [HermitianTraceFormVanishing.herm_smul_left, ihv, mul_zero]
    apply hξ0
    have hmv : X.Gm.mulVec (fun b => cc (ξ b)) = 0 := by
      funext a
      have := hall (Pi.single a 1)
      simpa [herm, Pi.single_apply, Matrix.mulVec, dotProduct] using this
    have h0 := Matrix.eq_zero_of_mulVec_eq_zero X.Gm_det hmv
    funext b
    have := congrFun h0 b
    simp only [Pi.zero_apply] at this
    have h2 := congrArg cc this
    simpa using h2
  set d : E := (X.den : E) with hd
  have hcint : IsIntegral ℤ (d * herm X.Gm η ξ) := X.Λ_int η hηΛ ξ hξΛ
  have hc0 : d * herm X.Gm η ξ ≠ 0 := by
    refine mul_ne_zero ?_ hηξ
    intro h
    apply X.den_ne
    simpa [hd] using h
  set c : E := d * herm X.Gm η ξ with hc
  let P : (X.Ψ → Fin r → ℂ) →ₗ[ℝ] (X.Ψ → Fin r → ℂ) :=
    { toFun := fun v τ => τ.1 c • v τ -
        (τ.1 d * hermC τ.1 X.Gm (v τ) (Data.emb τ.1 ξ)) • Data.emb τ.1 η
      map_add' := fun v v' => by
        funext τ
        simp only [Pi.add_apply, hermC_add_left, smul_add, mul_add, add_smul]
        abel
      map_smul' := fun a v => by
        funext τ
        simp only [Pi.smul_apply, RingHom.id_apply]
        rw [← Complex.coe_smul a (v τ), ← Complex.coe_smul a, hermC_smul_left]
        module }
  have hPΛ : ∀ l ∈ X.Λ, P (X.embV l) ∈ X.embV '' (X.Λp ξ : Set (Fin r → E)) := by
    intro l hl
    refine ⟨c • l - (d * herm X.Gm l ξ) • η, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_Λp_iff]
      refine ⟨X.Λ.sub_mem (smul_int_mem hcint hl) (smul_int_mem (X.Λ_int l hl ξ hξΛ) hηΛ), ?_⟩
      rw [HermitianTraceFormVanishing.herm_sub_left, HermitianTraceFormVanishing.herm_smul_left, HermitianTraceFormVanishing.herm_smul_left, hc]
      ring
    · funext τ b
      simp [P, Data.embV, Data.emb, hermC_emb]
  have hPv : P v = fun τ => τ.1 c • v τ := by
    funext τ
    simp only [P, LinearMap.coe_mk, AddHom.coe_mk]
    rw [hv τ, mul_zero, zero_smul, sub_zero]
  have hmem : P v ∈ Submodule.span ℝ (X.embV '' (X.Λp ξ : Set (Fin r → E))) := by
    have h1 := mem_span_Λ hD3 v
    have h2 : Submodule.map P (Submodule.span ℝ (X.embV '' (X.Λ : Set (Fin r → E)))) ≤
        Submodule.span ℝ (X.embV '' (X.Λp ξ : Set (Fin r → E))) := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
      exact Submodule.subset_span (hPΛ l hl)
    exact h2 (Submodule.mem_map_of_mem h1)
  rw [hPv] at hmem
  have h3 := scal_closed hD3 hmem (fun τ => (τ.1 c)⁻¹)
  convert h3 using 1
  funext τ
  rw [smul_smul, inv_mul_cancel₀ ((map_ne_zero τ.1).mpr hc0), one_smul]
end ReciprocityTheory.ChartRestriction.G.FD.LatticeSpanMembership
