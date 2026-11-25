-- Prove2me | solution 1 for PIW.FdPA.borel_flag_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:23:44.656013+00:00
-- url     : https://prove2.me/submissions/a0253f4d-9010-43ae-84c2-15e37aa9889f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_ZnNonneg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_Frames
import Theorems.Thm_PIW_FdPA_mem_dom_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PIW PIW.FdPA
open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex Metric
open scoped ComplexConjugate
noncomputable section
namespace PIW.FdPA
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] : BorFlag E := by
  classical
  intro r X x b hb hxb τ
  rw [mem_dom_iff] at hxb
  have hdet : (mat (rmul x b) τ).det ≠ 0 := (hxb τ).1
  have hdx : (mat x τ).det ≠ 0 := by
    intro h0
    apply hdet
    rw [show mat (rmul x b) τ = mat x τ * mat b τ from rfl, Matrix.det_mul, h0, zero_mul]

  have hcol : ∀ a, col (mat (rmul x b) τ) a = ∑ c, b τ c a • col (mat x τ) c := by
    intro a
    funext k
    simp [col, mat, rmul, Matrix.mul_apply, Finset.sum_apply, mul_comm]
    rfl
  have hli : ∀ y : Matrix (Fin r) (Fin r) ℂ, y.det ≠ 0 →
      LinearIndependent ℂ (fun a : Fin X.p0 => col y (Fin.castLE X.p0_le a)) := by
    intro y hy
    have h1 := Matrix.linearIndependent_cols_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det y).mpr (isUnit_iff_ne_zero.mpr hy))
    exact h1.comp (Fin.castLE X.p0_le) (Fin.castLE_injective _)
  have hle : Submodule.span ℂ (Set.range fun a : Fin X.p0 => col (mat (rmul x b) τ) (Fin.castLE X.p0_le a)) ≤
      Submodule.span ℂ (Set.range fun a : Fin X.p0 => col (mat x τ) (Fin.castLE X.p0_le a)) := by
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    simp only [hcol]
    refine Submodule.sum_mem _ (fun c _ => ?_)
    by_cases hc : (c : ℕ) < X.p0
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨c, hc⟩, rfl⟩)
    · have ha := a.isLt
      have hz : b τ c (Fin.castLE X.p0_le a) = 0 :=
        (hb τ).2 c (Fin.castLE X.p0_le a) (by rw [Fin.lt_iff_val_lt_val, Fin.coe_castLE]; omega)
      rw [hz, zero_smul]
      exact Submodule.zero_mem _
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  rw [finrank_span_eq_card (hli _ hdet), finrank_span_eq_card (hli _ hdx)]
end PIW.FdPA
