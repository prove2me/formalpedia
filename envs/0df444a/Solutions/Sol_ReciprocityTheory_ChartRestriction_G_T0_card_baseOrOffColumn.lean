-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.card_baseOrOffColumn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:29:47.518118+00:00
-- url     : https://prove2.me/submissions/c29c6b64-ddaa-4461-a1ee-4ca71f46db1a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraicIndependentResidueOfIsUnit
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValAlgebraMapEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {D N : ℕ} (j0 : Fin (N + 1)) :
    Fintype.card {e : TVar D N // e.1 = 0 ∨ e.2 ≠ j0} = (D + 1) * (N + 1) - D := by
  have hc := Fintype.card_subtype_compl (fun e : TVar D N => ¬ (e.1 = 0 ∨ e.2 ≠ j0))
  have e1 : {e : TVar D N // ¬ ¬ (e.1 = 0 ∨ e.2 ≠ j0)} ≃ {e : TVar D N // e.1 = 0 ∨ e.2 ≠ j0} :=
    Equiv.subtypeEquivRight (fun _ => not_not)
  have e2 : {e : TVar D N // ¬ (e.1 = 0 ∨ e.2 ≠ j0)} ≃ {i : Fin (D + 1) // i ≠ 0} :=
    { toFun := fun x => ⟨x.1.1, fun h => x.2 (Or.inl h)⟩
      invFun := fun i => ⟨(i.1, j0), fun h => h.elim i.2 (fun h' => h' rfl)⟩
      left_inv := fun x => by
        obtain ⟨⟨a, b⟩, hx⟩ := x
        have hb : b = j0 := by
          by_contra hne
          exact hx (Or.inr hne)
        subst hb
        rfl
      right_inv := fun i => rfl }
  rw [Fintype.card_congr e1, Fintype.card_congr e2] at hc
  have h3 : Fintype.card {i : Fin (D + 1) // i ≠ 0} = D := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fin]
    omega
  rw [hc, h3, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
end ReciprocityTheory.ChartRestriction.G.T0
