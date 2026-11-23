-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.MajorantNormalForms.Hf_sum_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:28:39.883796+00:00
-- url     : https://prove2.me/submissions/626402a1-6f16-40fa-ab82-4c8b45deb5b6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentCoefficientShift
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantNormalForms
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantNormalForms_ppos_sum
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
namespace MajorantNormalForms
open Matrix NumberField Complex
open scoped ComplexConjugate ComplexOrder
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
private lemma hermC_sum_left_lemma {ι : Type} [Fintype ι] (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (u : ι → ℂ) (v : ι → Fin r → ℂ) (y : Fin r → ℂ) :
    hermC τ G (∑ k, u k • v k) y = ∑ k, u k * hermC τ G (v k) y := by
  let f : (Fin r → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun x => hermC τ G x y
      map_add' := fun x x' => by
        simp only [hermC, Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        simp only [hermC, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring }
  have h := map_sum f (fun k => u k • v k) Finset.univ
  simp only [map_smul, smul_eq_mul] at h
  exact h
private lemma hermC_sum_right_lemma_2 {ι : Type} [Fintype ι] (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (x : Fin r → ℂ) (w : ι → ℂ) (z : ι → Fin r → ℂ) :
    hermC τ G x (∑ l, w l • z l) = ∑ l, conj (w l) * hermC τ G x (z l) := by
  let g : (Fin r → ℂ) →ₗ⋆[ℂ] ℂ :=
    { toFun := fun y => hermC τ G x y
      map_add' := fun y y' => by
        simp only [hermC, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c y => by
        simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring }
  have h := map_sum g (fun l => w l • z l) Finset.univ
  simp only [map_smulₛₗ, smul_eq_mul] at h
  exact h
end MajorantNormalForms
end ReciprocityTheory.ChartRestriction.G.FD
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.MajorantNormalForms
open Matrix NumberField Complex
open scoped ComplexConjugate ComplexOrder
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.MajorantNormalForms
theorem _root_.solution (x : Frame X.Ψ r) (τ : X.Ψ) (c d : Fin r → ℂ) (u w : Fin r → Fin r → ℂ) :
    X.Hf x τ (∑ a, c a • u a) (∑ b, d b • w b) =
      ∑ a, ∑ b, c a * conj (d b) * X.Hf x τ (u a) (w b) := by
  have hz : (2 : ℂ) • X.ppos x τ (∑ a, c a • u a) - ∑ a, c a • u a =
      ∑ a, c a • ((2 : ℂ) • X.ppos x τ (u a) - u a) := by
    rw [ppos_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [smul_sub, smul_comm]
  unfold Data.Hf
  rw [hz, hermC_sum_left_lemma]
  simp only [hermC_sum_right_lemma_2]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring
end ReciprocityTheory.ChartRestriction.G.FD.MajorantNormalForms
