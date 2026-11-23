-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.Hf_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:20:50.583527+00:00
-- url     : https://prove2.me/submissions/c2f353ea-4474-492a-a54e-6000e76cc276

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnitaryComplementMoveOfIsotropic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_Hf_eq_two_ppos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_gramPos_isHermitian
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_hermC_ppos_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_conj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate ComplexOrder
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.Data
theorem _root_.solution {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) :
    X.Hf x τ v v = (X.maj x τ v : ℂ) := by
  have hG := X.Gm_herm
  have hAi : ((X.gramPos x τ)⁻¹).IsHermitian := (X.gramPos_isHermitian x τ).inv
  have hM : ∀ a b, conj ((X.gramPos x τ)⁻¹ b a) = (X.gramPos x τ)⁻¹ a b := fun a b => hAi.apply a b
  have hS : ∀ u : Fin X.p0 → ℂ, conj (∑ a, ∑ b, u a * (X.gramPos x τ)⁻¹ a b * conj (u b)) =
      ∑ a, ∑ b, u a * (X.gramPos x τ)⁻¹ a b * conj (u b) := by
    intro u
    simp only [map_sum, map_mul, Complex.conj_conj]
    refine Finset.sum_comm.trans (Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_)
    rw [hM]
    ring
  have e1 : (((∑ a, ∑ b, hermC τ.1 X.Gm v (X.colP x τ a) * (X.gramPos x τ)⁻¹ a b *
      conj (hermC τ.1 X.Gm v (X.colP x τ b))).re : ℝ) : ℂ) =
      ∑ a, ∑ b, hermC τ.1 X.Gm v (X.colP x τ a) * (X.gramPos x τ)⁻¹ a b *
      conj (hermC τ.1 X.Gm v (X.colP x τ b)) := Complex.conj_eq_iff_re.mp (hS _)
  have e2 : (((hermC τ.1 X.Gm v v).re : ℝ) : ℂ) = hermC τ.1 X.Gm v v :=
    Complex.conj_eq_iff_re.mp (ReciprocityTheory.ChartRestriction.G.FD.hermC_conj τ.1 hG v v)
  have hpp : X.posPart x τ v = (∑ a, ∑ b, hermC τ.1 X.Gm v (X.colP x τ a) * (X.gramPos x τ)⁻¹ a b *
      conj (hermC τ.1 X.Gm v (X.colP x τ b))).re := rfl
  have hmj : X.maj x τ v = 2 * X.posPart x τ v - (hermC τ.1 X.Gm v v).re := rfl
  rw [X.Hf_eq_two_ppos, X.hermC_ppos_self, hmj, hpp, Complex.ofReal_sub, Complex.ofReal_mul, e1, e2]
  norm_num
end ReciprocityTheory.ChartRestriction.G.FD.Data
