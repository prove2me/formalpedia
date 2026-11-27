-- Prove2me | solution 1 for P2M_Formalism_L2_Pj_divFin_of_lawA3__ca8ab2190a30
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:51:13.896025+00:00
-- url     : https://prove2.me/submissions/d95d2b51-e2f7-4060-ac0c-31950b3f3a51

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompHt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_DivFinOfLawA3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Fintype (Comp Xo c)]
variable (d : Data c.F (Comp Xo c) (fun Z => Om Z) (WTZ E) (fun Z => AC Z))
namespace Formalism.L2.Pj
theorem _root_.solution (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (hord : ∀ Z v, d.ord Z v = ordC (δ Z v) v) (h : LawA3' d) : DivFin d := by
  intro Z r hr
  have hmem : AddMonoidAlgebra.single (0 : WTZ E) r ∈ AG Z 0 := by
    refine Submodule.mem_span_singleton.mpr ⟨r, ?_⟩
    first
      | simp [AddMonoidAlgebra.smul_single']
      | (rw [AddMonoidAlgebra.smul_single', mul_one])
  have hne0 : AddMonoidAlgebra.single (0 : WTZ E) r ≠ 0 := by
    first
      | simpa using hr
      | exact Finsupp.single_ne_zero.mpr hr
  refine (h Z hmem hne0).subset ?_
  rintro v ⟨hadm, hv⟩
  refine ⟨hadm, ?_⟩
  rw [hord]
  unfold ordC
  have hc : (AddMonoidAlgebra.single (0 : WTZ E) r).coeff 0 = r := by
    first
      | simp
      | rfl
  have hf0 : frW (δ Z v) (0 : WTZ E) = 0 := by
    unfold frW
    refine Finset.sum_eq_zero (fun i _ => ?_)
    cases i <;> simp [exZ]
  rw [hc, hf0, add_zero]
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp ((AddValuation.top_iff v).not.mpr hr)
  rw [← hn, WithTop.untopD_coe]
  rintro rfl
  exact hv (by rw [← hn]; rfl)
end Formalism.L2.Pj
