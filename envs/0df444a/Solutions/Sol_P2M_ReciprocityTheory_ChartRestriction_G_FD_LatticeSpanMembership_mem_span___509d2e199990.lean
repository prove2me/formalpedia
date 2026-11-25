-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_FD_LatticeSpanMembership_mem_span___509d2e199990
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:23:17.645797+00:00
-- url     : https://prove2.me/submissions/d531a5c6-f34c-499a-bb22-34e96b9a7ce7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantOperators
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LatticeSpanMembership
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_LatticeSpanMembership_span_emb_int
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_LatticeSpanMembership_exists_nat_smul_mem
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
theorem _root_.solution (hD3 : IntegerApproximationCount (E := E)) (v : X.Ψ → Fin r → ℂ) :
    v ∈ Submodule.span ℝ (X.embV '' (X.Λ : Set (Fin r → E))) := by
  classical
  have hsing : ∀ (a : Fin r) (s : X.Ψ → ℂ),
      single (X := X) a s ∈ Submodule.span ℝ (X.embV '' (X.Λ : Set (Fin r → E))) := by
    intro a s
    obtain ⟨N, hN, hNmem⟩ := exists_nat_smul_mem (X := X) (Pi.single a 1)
    have hgen : Submodule.span ℝ (Set.range fun α : 𝓞 E => fun τ : X.Ψ => τ.1 (α : E)) ≤
        (Submodule.span ℝ (X.embV '' (X.Λ : Set (Fin r → E)))).comap (single (X := X) a) := by
      rw [Submodule.span_le]
      rintro _ ⟨α, rfl⟩
      have hmem : (α : E) • ((N : E) • Pi.single a 1) ∈ X.Λ := smul_int_mem α.isIntegral_coe hNmem
      have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      have e : single (X := X) a (fun τ : X.Ψ => τ.1 (α : E)) =
          (N : ℝ)⁻¹ • X.embV ((α : E) • ((N : E) • Pi.single a 1)) := by
        funext τ b
        simp only [single, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, Data.embV, Data.emb,
          smul_eq_mul]
        by_cases hb : b = a
        · subst hb
          have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
          simp only [Pi.single_eq_same, mul_one, map_mul, map_natCast, Complex.real_smul]
          push_cast
          field_simp
        · simp [Pi.single_eq_of_ne hb]
      rw [SetLike.mem_coe, Submodule.mem_comap]
      show single (X := X) a (fun τ : X.Ψ => τ.1 (α : E)) ∈ _
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hmem, rfl⟩)
    exact hgen (x := s) (by rw [span_emb_int hD3]; exact Submodule.mem_top)
  have hv : v = ∑ a : Fin r, single (X := X) a (fun τ => v τ a) := by
    funext τ b
    rw [Finset.sum_apply, Finset.sum_apply]
    simp only [single, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.sum_eq_single b (fun a _ hab => by rw [Pi.single_apply, if_neg (Ne.symm hab)])
      (fun h => absurd (Finset.mem_univ b) h), Pi.single_eq_same]
  rw [hv]
  exact Submodule.sum_mem _ fun a _ => hsing a _
end ReciprocityTheory.ChartRestriction.G.FD.LatticeSpanMembership
