-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalPerpBasis_sum_split__579f930c6f43
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:15:47.977428+00:00
-- url     : https://prove2.me/submissions/aac8edf0-2937-4278-9b72-20a094539971

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OnbPerp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PosCoordNe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HCSumRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis
open NumberField Complex Matrix
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis
theorem _root_.solution {M : Type*} [AddCommMonoid M] (f : Fin r → M) :
    ∑ j, f j = ∑ a : Fin X.p0, f (Fin.castLE X.p0_le a) +
      ∑ m : Fin (r - X.p0), f ⟨X.p0 + m, by have := m.isLt; have := X.p0_le; omega⟩ := by
  obtain ⟨g, hg⟩ : ∃ g : ℕ → M, ∀ j (h : j < r), g j = f ⟨j, h⟩ :=
    ⟨fun j => if h : j < r then f ⟨j, h⟩ else 0, fun j h => dif_pos h⟩
  have h1 : ∑ j, f j = ∑ j : Fin r, g j :=
    Finset.sum_congr rfl fun j _ => (hg j j.isLt).symm
  have h2 : ∑ a : Fin X.p0, f (Fin.castLE X.p0_le a) = ∑ a : Fin X.p0, g a :=
    Finset.sum_congr rfl fun a _ => (hg a (lt_of_lt_of_le a.isLt X.p0_le)).symm
  have h3 : ∑ m : Fin (r - X.p0), f ⟨X.p0 + m, by have := m.isLt; have := X.p0_le; omega⟩ =
      ∑ m : Fin (r - X.p0), g (X.p0 + m) :=
    Finset.sum_congr rfl fun m _ =>
      (hg (X.p0 + m) (by have := m.isLt; have := X.p0_le; omega)).symm
  rw [h1, h2, h3, Fin.sum_univ_eq_sum_range g r, Fin.sum_univ_eq_sum_range g X.p0,
    Fin.sum_univ_eq_sum_range (fun m => g (X.p0 + m)) (r - X.p0)]
  conv_lhs => rw [← Nat.add_sub_of_le X.p0_le]
  exact Finset.sum_range_add g X.p0 (r - X.p0)
end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis
