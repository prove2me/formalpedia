-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.LatticeSpanMembership.exists_nat_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:08:52.976946+00:00
-- url     : https://prove2.me/submissions/36d0e3ed-1f41-4c6c-9557-0b2ed99685ca

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantOperators
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LatticeSpanMembership
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_LatticeSpanMembership_exists_nat_mul_int
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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantOperators_add_mem
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
theorem _root_.solution (v : Fin r → E) : ∃ N : ℕ, 0 < N ∧ (N : E) • v ∈ X.Λ := by
  have hv : v ∈ Submodule.span E (X.Λ : Set (Fin r → E)) := X.Λ_span ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem v hv => exact ⟨1, one_pos, by simpa using hv⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add v w _ _ ihv ihw =>
    obtain ⟨N1, h1, hv1⟩ := ihv
    obtain ⟨N2, h2, hw2⟩ := ihw
    refine ⟨N1 * N2, Nat.mul_pos h1 h2, ?_⟩
    have e : ((N1 * N2 : ℕ) : E) • (v + w) = N2 • ((N1 : E) • v) + N1 • ((N2 : E) • w) := by
      rw [← Nat.cast_smul_eq_nsmul E N2, ← Nat.cast_smul_eq_nsmul E N1, smul_smul, smul_smul,
        smul_add, Nat.cast_mul, mul_comm (N2 : E)]
    rw [e]
    exact X.Λ.add_mem (X.Λ.toAddSubmonoid.nsmul_mem hv1 N2) (X.Λ.toAddSubmonoid.nsmul_mem hw2 N1)
  | smul c v _ ihv =>
    obtain ⟨N, hN, hv⟩ := ihv
    obtain ⟨M, hM, hc⟩ := exists_nat_mul_int c
    refine ⟨M * N, Nat.mul_pos hM hN, ?_⟩
    obtain ⟨γ, hγ⟩ : ∃ γ : 𝓞 E, (γ : E) = (M : E) * c := ⟨⟨_, hc⟩, rfl⟩
    have h := X.Λ.smul_mem γ hv
    rw [← algebraMap_smul E γ ((N : E) • v)] at h
    convert h using 1
    show ((M * N : ℕ) : E) • (c • v) = (γ : E) • ((N : E) • v)
    rw [hγ, smul_smul, smul_smul]
    congr 1
    push_cast
    ring
end ReciprocityTheory.ChartRestriction.G.FD.LatticeSpanMembership
