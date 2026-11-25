-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf.posPart_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:38:58.729802+00:00
-- url     : https://prove2.me/submissions/6c562d94-a18b-462c-8bc5-f2fcad8efb3e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtDataPfA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TorusAtDataPf_proj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TorusAtDataPf_gramPos_det_ne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_gramPos_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_hermC_ppos_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_ppos_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_sum_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_sum_right


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r) (τ : X.Ψ) (e : Fin r → Fin r → ℂ)
  (he : ∀ a b, hermC τ.1 X.Gm (e a) (e b) = if a = b then ((sgn X.p0 a : ℝ) : ℂ) else 0)
  (x : Frame X.Ψ r)
  (hflag : Submodule.span ℂ (Set.range fun a : Fin X.p0 => e (Fin.castLE X.p0_le a)) =
      Submodule.span ℂ (Set.range fun a : Fin X.p0 => X.colP x τ a))
  (hind : LinearIndependent ℂ (X.colP x τ))
include he hflag hind
namespace ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf
theorem _root_.solution (u : Fin r → ℂ) :
    X.posPart x τ u = ∑ a : Fin X.p0, ‖hermC τ.1 X.Gm u (e (Fin.castLE X.p0_le a))‖ ^ 2 := by
  have hdet := gramPos_det_ne X τ e he x hflag hind
  have hG : (X.gramPos x τ)⁻¹ * X.gramPos x τ = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet)
  have hA : ∀ d, hermC τ.1 X.Gm (X.ppos x τ u) (X.colP x τ d) = hermC τ.1 X.Gm u (X.colP x τ d) := by
    intro d
    rw [Data.ppos_eq, hermC_sum_left]
    simp only [hermC_smul_left, ← Data.gramPos_apply]
    have hs : ∑ a : Fin X.p0, (∑ b : Fin X.p0, hermC τ.1 X.Gm u (X.colP x τ b) *
        (X.gramPos x τ)⁻¹ b a) * X.gramPos x τ a d
        = ∑ b : Fin X.p0, hermC τ.1 X.Gm u (X.colP x τ b) *
          ((X.gramPos x τ)⁻¹ * X.gramPos x τ) b d := by
      simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
      exact Finset.sum_comm
    rw [hs, hG]
    simp [Matrix.one_apply]
  have hmemC : ∀ y ∈ Submodule.span ℂ (Set.range fun a : Fin X.p0 => X.colP x τ a),
      hermC τ.1 X.Gm (X.ppos x τ u) y = hermC τ.1 X.Gm u y := by
    intro y hy
    obtain ⟨δ, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hy
    simp only [hermC_sum_right, hermC_smul_right, hA]
  have hp : X.ppos x τ u ∈
      Submodule.span ℂ (Set.range fun a : Fin X.p0 => e (Fin.castLE X.p0_le a)) := by
    rw [hflag, Data.ppos_eq]
    exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
  have hpe := proj X τ e he (X.ppos x τ u) hp
  have hcoef : ∀ a : Fin X.p0, hermC τ.1 X.Gm (X.ppos x τ u) (e (Fin.castLE X.p0_le a))
      = hermC τ.1 X.Gm u (e (Fin.castLE X.p0_le a)) := fun a =>
    hmemC _ (by rw [← hflag]; exact Submodule.subset_span ⟨a, rfl⟩)
  simp_rw [hcoef] at hpe
  have h1 : X.posPart x τ u = (hermC τ.1 X.Gm (X.ppos x τ u) u).re := by
    rw [Data.hermC_ppos_self]; rfl
  rw [h1, hpe, hermC_sum_left, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hermC_smul_left, ← hermC_conj τ.1 X.Gm_herm u (e (Fin.castLE X.p0_le a)),
    Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
end ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf
