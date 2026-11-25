-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.hermitian_dual_lattice_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:39:44.270831+00:00
-- url     : https://prove2.me/submissions/6c0c32e6-8496-4eee-8273-6d89a88234d5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermEqZeroOfTraceFormVanish
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_mem_orthogonal_lattice_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_integer_smul_eq_coe_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_herm_eq_zero_of_trace_form_vanish
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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_exists_eq_smul_of_herm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_exists_smul_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_herm_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_herm_smul_right
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
open NumberField ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
namespace ReciprocityTheory.ChartRestriction.G.FD
theorem _root_.solution : PerfectPairingQuotient (E := E) := by
  intro r X ξ hξ
  obtain ⟨hξΛ, hξξ, hξ0⟩ := hξ
  have hsm : ∀ (β : 𝓞 E) v, v ∈ X.Λp ξ → β • v ∈ X.Λp ξ := by
    intro β v hv
    rw [mem_orthogonal_lattice_iff] at hv ⊢
    refine ⟨X.Λ.smul_mem β hv.1, ?_⟩
    rw [integer_smul_eq_coe_smul, herm_smul_left, hv.2, mul_zero]
  have hξp : ξ ∈ X.Λp ξ := (mem_orthogonal_lattice_iff _ _ _).mpr ⟨hξΛ, hξξ⟩
  constructor
  · intro φ hφ
    have : Module.Finite (𝓞 E) ↥X.Λ := Module.Finite.iff_fg.mpr X.Λ_fg
    have : Module.Finite ℤ ↥X.Λ := Module.Finite.trans (𝓞 E) ↥X.Λ
    let f : ↥X.Λ →ₗ[ℤ] E := ((X.hermL ξ).comp X.Λ.subtype.toAddMonoidHom).toIntLinearMap
    have hf : ∀ m : ↥X.Λ, f m = herm X.Gm (m : Fin r → E) ξ := fun m => rfl
    let P := LinearMap.ker f
    have : Module.IsTorsionFree ℤ (↥X.Λ ⧸ P) := by
      rw [Module.isTorsionFree_iff_smul_eq_zero]
      intro n q hq
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective P q
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, LinearMap.mem_ker,
        map_zsmul] at hq
      rcases smul_eq_zero.mp hq with h | h
      · exact Or.inl h
      · exact Or.inr ((Submodule.Quotient.mk_eq_zero P).mpr (LinearMap.mem_ker.mpr h))
    obtain ⟨s, hs⟩ := Module.projective_lifting_property P.mkQ LinearMap.id P.mkQ_surjective
    have hsq : ∀ q, P.mkQ (s q) = q := fun q => LinearMap.congr_fun hs q
    have hρ : ∀ m : ↥X.Λ, m - s (P.mkQ m) ∈ P := by
      intro m
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]
      change P.mkQ m - P.mkQ (s (P.mkQ m)) = 0
      rw [hsq, sub_self]
    let ψ : ↥X.Λ →+ ℤ :=
      { toFun := fun m => φ ⟨((m - s (P.mkQ m) : ↥X.Λ) : Fin r → E),
          (mem_orthogonal_lattice_iff _ _ _).mpr ⟨(m - s (P.mkQ m)).2, LinearMap.mem_ker.mp (hρ m)⟩⟩
        map_zero' := by
          rw [← map_zero φ]; congr 1; ext1; simp
        map_add' := by
          intro a b
          rw [← map_add φ]; congr 1; ext1
          simp only [map_add]
          push_cast
          abel }
    obtain ⟨x, hxΛ, hx⟩ := X.EF_perf ψ
    have hval : ∀ ν : X.Λp ξ, (φ ν : ℚ) = EFf X.ξ0 X.Gm x ν := by
      intro ν
      have hν := (mem_orthogonal_lattice_iff _ _ _).mp ν.2
      have hP : (⟨ν, hν.1⟩ : ↥X.Λ) ∈ P := by rw [LinearMap.mem_ker, hf]; exact hν.2
      have hmk : P.mkQ (⟨ν, hν.1⟩ : ↥X.Λ) = 0 := (Submodule.Quotient.mk_eq_zero P).mpr hP
      have hψ : ψ ⟨ν, hν.1⟩ = φ ν := by
        show φ _ = φ ν
        congr 1; ext1
        simp [hmk]
      rw [← hψ]; exact hx ⟨ν, hν.1⟩
    have hxξ : herm X.Gm x ξ = 0 := by
      apply herm_eq_zero_of_trace_form_vanish X.ξ0 X.ξ0_ne
      intro β
      have hmem := hsm β ξ hξp
      have h0 := hφ ⟨β • ξ, hmem⟩ ⟨(β : E), integer_smul_eq_coe_smul β ξ⟩
      have h1 := hval ⟨β • ξ, hmem⟩
      rw [h0] at h1
      simpa using h1.symm
    exact ⟨⟨x, (mem_orthogonal_lattice_iff _ _ _).mpr ⟨hxΛ, hxξ⟩⟩, hval⟩
  · intro μ hμ
    apply exists_eq_smul_of_herm X.Gm X.Gm_det X.Gm_herm ξ μ hξ0
    intro y hy
    have horth : ∀ ν ∈ X.Λp ξ, herm X.Gm μ ν = 0 := by
      intro ν hν
      apply herm_eq_zero_of_trace_form_vanish X.ξ0 X.ξ0_ne
      intro β
      exact hμ ⟨β • ν, hsm β ν hν⟩
    obtain ⟨d, hd, hdy⟩ := exists_smul_mem (F := E) X.Λ (x := y)
      (by rw [X.Λ_span]; exact Submodule.mem_top)
    have hdyp : d • y ∈ X.Λp ξ := by
      rw [mem_orthogonal_lattice_iff]
      refine ⟨hdy, ?_⟩
      rw [integer_smul_eq_coe_smul, herm_smul_left, hy, mul_zero]
    have h2 := horth _ hdyp
    rw [integer_smul_eq_coe_smul, herm_smul_right] at h2
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h (by simpa using hd)
    · exact h
end ReciprocityTheory.ChartRestriction.G.FD
