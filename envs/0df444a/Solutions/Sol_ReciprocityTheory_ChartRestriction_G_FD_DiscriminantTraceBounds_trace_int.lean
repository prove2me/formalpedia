-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.DiscriminantTraceBounds.trace_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:01:19.370191+00:00
-- url     : https://prove2.me/submissions/46480fdd-3afe-40bb-b1fe-ea1c89e978a3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DiscriminantTraceBounds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_DiscriminantTraceBounds_exists_herm_ne
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


section
namespace ReciprocityTheory.ChartRestriction.G.FD
namespace DiscriminantTraceBounds
open NumberField Complex Module Matrix
open scoped ComplexConjugate nonZeroDivisors
variable {E : Type} [Field E] [NumberField E]
section data
variable [IsCMField E] {r : ℕ} (X : DataX E r)
private theorem herm_smul_left_eq_mul (G : Matrix (Fin r) (Fin r) E) (c : E) (x y : Fin r → E) :
    herm G (c • x) y = c * herm G x y := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
private theorem herm_smul_right_fundamental_domains (G : Matrix (Fin r) (Fin r) E) (c : E) (x y : Fin r → E) :
    herm G x (c • y) = cc c * herm G x y := by
  have hcc_mul : ∀ a b : E, cc (a * b) = cc a * cc b := fun a b => by
    unfold cc
    exact map_mul _ a b
  simp only [herm, Pi.smul_apply, smul_eq_mul, hcc_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
end data
end DiscriminantTraceBounds
end ReciprocityTheory.ChartRestriction.G.FD
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.DiscriminantTraceBounds
open NumberField Complex Module Matrix
open scoped ComplexConjugate nonZeroDivisors
variable {E : Type} [Field E] [NumberField E]
variable [IsCMField E] {r : ℕ} (X : DataX E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.DiscriminantTraceBounds
theorem _root_.solution (hr : 0 < r) (c : 𝓞 E) :
    ∃ m : ℤ, Algebra.trace ℚ E ((X.NC : E) ^ 2 * X.ξ0 * c) = m := by
  classical
  set gens : Set (𝓞 E) := {c | ∃ x ∈ X.L', ∃ y ∈ X.L', (c : E) = herm X.Gm x y} with hgens
  set J : Ideal (𝓞 E) := Ideal.span gens with hJdef
  have hgen_mem : ∀ x ∈ X.L', ∀ y ∈ X.L', ∃ c ∈ J, (c : E) = herm X.Gm x y := by
    intro x hx y hy
    exact ⟨⟨herm X.Gm x y, X.L'_int x hx y hy⟩, Ideal.subset_span ⟨x, hx, y, hy, rfl⟩, rfl⟩
  have hJ0 : J ≠ ⊥ := by
    obtain ⟨x, hx, y, hy, hne⟩ := exists_herm_ne X hr
    obtain ⟨c, hc, hce⟩ := hgen_mem x hx y hy
    intro hbot
    rw [hbot, Ideal.mem_bot] at hc
    apply hne
    rw [← hce, hc]
    simp
  have hJf0 : (J : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    exact hJ0
  have hmemJf : ∀ c ∈ J, ((c : 𝓞 E) : E) ∈ (J : FractionalIdeal (𝓞 E)⁰ E) :=
    fun c hc => (FractionalIdeal.mem_coeIdeal _).mpr ⟨c, hc, rfl⟩
  have hinv : ∀ t ∈ (J : FractionalIdeal (𝓞 E)⁰ E)⁻¹, ∀ x ∈ X.L', t • x ∈ X.L' := by
    intro t ht x hx
    apply X.L'_dual
    intro y hy
    rw [herm_smul_left_eq_mul]
    obtain ⟨c, hc, hce⟩ := hgen_mem x hx y hy
    have h1 := (FractionalIdeal.mem_inv_iff hJf0).mp ht _ (hmemJf c hc)
    obtain ⟨d, hd⟩ := (FractionalIdeal.mem_one_iff _).mp h1
    rw [← hce, ← hd]
    exact RingOfIntegers.isIntegral_coe d
  have hmul : ∀ t ∈ (J : FractionalIdeal (𝓞 E)⁰ E)⁻¹, ∀ c ∈ J,
      t * (c : E) ∈ (J : FractionalIdeal (𝓞 E)⁰ E) := by
    intro t ht c hc
    induction hc using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨x, hx, y, hy, hce⟩ := hc
      rw [hce, ← herm_smul_left_eq_mul]
      obtain ⟨c', hc', hce'⟩ := hgen_mem _ (hinv t ht x hx) y hy
      rw [← hce']
      exact hmemJf c' hc'
    | zero =>
      simp
    | add a b _ _ ha hb =>
      push_cast
      rw [mul_add]
      exact Submodule.add_mem _ ha hb
    | smul a c _ h =>
      rw [smul_eq_mul]
      push_cast
      rw [mul_left_comm, ← Algebra.smul_def]
      exact Submodule.smul_mem _ a h
  have hle : (J : FractionalIdeal (𝓞 E)⁰ E)⁻¹ * (J : FractionalIdeal (𝓞 E)⁰ E) ≤
      (J : FractionalIdeal (𝓞 E)⁰ E) := FractionalIdeal.mul_le.mpr fun t ht j hj => by
    obtain ⟨c, hc, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hj
    exact hmul t ht c hc
  rw [inv_mul_cancel₀ hJf0] at hle
  have hJtop : J = ⊤ := by
    rw [eq_top_iff]
    rw [← FractionalIdeal.coeIdeal_top] at hle
    exact (FractionalIdeal.coeIdeal_le_coeIdeal E).mp hle
  have hccNC : cc (X.NC : E) = X.NC := by
    unfold cc
    exact map_natCast _ _
  have hP : ∀ c ∈ J, ∀ a : 𝓞 E, ∃ m : ℤ,
      Algebra.trace ℚ E ((X.NC : E) ^ 2 * X.ξ0 * ((a : E) * (c : E))) = m := by
    intro c hc
    induction hc using Submodule.span_induction with
    | mem c hc =>
      intro a
      obtain ⟨x, hx, y, hy, hce⟩ := hc
      have hax : (a : E) • x ∈ X.L' := by
        rw [show (a : E) • x = a • x from algebraMap_smul E a x]
        exact X.L'.smul_mem a hx
      obtain ⟨k, hk⟩ := X.EF_int _ (X.NC_sub _ hax) _ (X.NC_sub _ hy)
      refine ⟨-k, ?_⟩
      unfold EFf at hk
      rw [herm_smul_left_eq_mul, herm_smul_right_fundamental_domains, herm_smul_left_eq_mul, hccNC] at hk
      have h2 : (X.NC : E) ^ 2 * X.ξ0 * ((a : E) * (c : E)) =
          -(-X.ξ0 * ((X.NC : E) * ((X.NC : E) * ((a : E) * herm X.Gm x y)))) := by
        rw [hce]
        ring
      rw [h2, map_neg, hk]
      push_cast
      ring
    | zero =>
      intro a
      exact ⟨0, by simp⟩
    | add c c' _ _ h1 h2 =>
      intro a
      obtain ⟨m1, hm1⟩ := h1 a
      obtain ⟨m2, hm2⟩ := h2 a
      refine ⟨m1 + m2, ?_⟩
      push_cast
      rw [mul_add, mul_add, map_add, hm1, hm2]
    | smul b c _ h =>
      intro a
      obtain ⟨m, hm⟩ := h (a * b)
      refine ⟨m, ?_⟩
      rw [← hm, smul_eq_mul]
      push_cast
      ring_nf
  obtain ⟨m, hm⟩ := hP c (by rw [hJtop]; exact Submodule.mem_top) 1
  refine ⟨m, ?_⟩
  rw [← hm]
  simp
end ReciprocityTheory.ChartRestriction.G.FD.DiscriminantTraceBounds
