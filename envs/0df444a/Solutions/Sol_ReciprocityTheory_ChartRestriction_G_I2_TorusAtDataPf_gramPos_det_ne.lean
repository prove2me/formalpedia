-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf.gramPos_det_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:30:56.178575+00:00
-- url     : https://prove2.me/submissions/89006bfa-baf8-4fd2-af55-f9ea0112b646

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtDataPfA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TorusAtDataPf_proj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_gramPos_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_right
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
theorem _root_.solution : (X.gramPos x τ).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  obtain ⟨w, hw⟩ : ∃ w : Fin r → ℂ, w = ∑ b : Fin X.p0, conj (v b) • X.colP x τ b := ⟨_, rfl⟩
  have h1 : ∀ a, hermC τ.1 X.Gm (X.colP x τ a) w = 0 := by
    intro a
    have ha := congrFun hv a
    simp only [Matrix.mulVec, dotProduct, Data.gramPos_apply, Pi.zero_apply] at ha
    rw [hw, hermC_sum_right]
    simp only [hermC_smul_right, Complex.conj_conj]
    rw [← ha]
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  have h2 : ∀ a, hermC τ.1 X.Gm w (X.colP x τ a) = 0 := fun a => by
    rw [← hermC_conj τ.1 X.Gm_herm (X.colP x τ a) w, h1, map_zero]
  have h3 : ∀ y ∈ Submodule.span ℂ (Set.range fun a : Fin X.p0 => X.colP x τ a),
      hermC τ.1 X.Gm w y = 0 := by
    intro y hy
    obtain ⟨δ, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hy
    simp [hermC_sum_right, hermC_smul_right, h2]
  have hwf : w ∈ Submodule.span ℂ (Set.range fun a : Fin X.p0 => e (Fin.castLE X.p0_le a)) := by
    rw [hflag, hw]
    exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
  have hw0 : w = 0 := by
    rw [proj X τ e he w hwf]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [h3 _ (by rw [← hflag]; exact Submodule.subset_span ⟨a, rfl⟩), zero_smul]
  have hz := Fintype.linearIndependent_iff.mp hind (fun b => conj (v b)) (hw ▸ hw0)
  apply hv0
  funext b
  simpa using hz b
end ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf
