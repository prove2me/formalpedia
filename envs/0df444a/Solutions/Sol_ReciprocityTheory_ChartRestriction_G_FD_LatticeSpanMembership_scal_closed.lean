-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.LatticeSpanMembership.scal_closed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:02:32.199414+00:00
-- url     : https://prove2.me/submissions/8697259b-4b77-4b06-8429-b56435c77551

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantOperators
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LatticeSpanMembership
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_LatticeSpanMembership_span_emb_int
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_LatticeSpanMembership_mem__p_iff_0da98c18e74b
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_LatticeSpanMembership_smul_int_mem
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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_herm_smul_left
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
theorem _root_.solution (hD3 : IntegerApproximationCount (E := E)) {ξ : Fin r → E} {w : X.Ψ → Fin r → ℂ}
    (hw : w ∈ Submodule.span ℝ (X.embV '' (X.Λp ξ : Set (Fin r → E)))) (s : X.Ψ → ℂ) :
    (fun τ => s τ • w τ) ∈ Submodule.span ℝ (X.embV '' (X.Λp ξ : Set (Fin r → E))) := by
  set W := Submodule.span ℝ (X.embV '' (X.Λp ξ : Set (Fin r → E))) with hW

  have hα : ∀ (α : 𝓞 E), ∀ v ∈ W, (fun τ : X.Ψ => τ.1 (α : E) • v τ) ∈ W := by
    intro α
    let M : (X.Ψ → Fin r → ℂ) →ₗ[ℝ] (X.Ψ → Fin r → ℂ) :=
      { toFun := fun v τ => τ.1 (α : E) • v τ
        map_add' := fun v v' => by funext τ; simp [smul_add]
        map_smul' := fun c v => by
          funext τ
          show τ.1 (α : E) • (c • v τ) = c • (τ.1 (α : E) • v τ)
          exact smul_comm _ _ _ }
    have hle : W ≤ W.comap M := by
      rw [hW, Submodule.span_le]
      rintro _ ⟨μ, hμ, rfl⟩
      rw [SetLike.mem_coe, mem_Λp_iff] at hμ
      have hαμ : (α : E) • μ ∈ X.Λp ξ := by
        rw [mem_Λp_iff]
        exact ⟨smul_int_mem α.isIntegral_coe hμ.1, by rw [HermitianTraceFormVanishing.herm_smul_left, hμ.2, mul_zero]⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      have e : M (X.embV μ) = X.embV ((α : E) • μ) := by
        funext τ b
        simp [M, Data.embV, Data.emb]
      rw [e]
      exact Submodule.subset_span ⟨_, hαμ, rfl⟩
    intro v hv
    exact hle hv
  let T : (X.Ψ → ℂ) →ₗ[ℝ] (X.Ψ → Fin r → ℂ) :=
    { toFun := fun s τ => s τ • w τ
      map_add' := fun s s' => by funext τ; simp [add_smul]
      map_smul' := fun c s => by
        funext τ
        simp only [Pi.smul_apply, RingHom.id_apply, Complex.real_smul]
        rw [← Complex.coe_smul c (s τ • w τ), smul_smul] }
  have hle : Submodule.span ℝ (Set.range fun α : 𝓞 E => fun τ : X.Ψ => τ.1 (α : E)) ≤ W.comap T := by
    rw [Submodule.span_le]
    rintro _ ⟨α, rfl⟩
    exact hα α w hw
  exact hle (x := s) (by rw [span_emb_int hD3]; exact Submodule.mem_top)
end ReciprocityTheory.ChartRestriction.G.FD.LatticeSpanMembership
