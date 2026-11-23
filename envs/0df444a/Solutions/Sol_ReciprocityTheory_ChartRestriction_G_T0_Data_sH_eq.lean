-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.sH_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:48:08.396187+00:00
-- url     : https://prove2.me/submissions/caf086ef-203c-4e72-8eed-7366e254a79c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SacSuccAbove

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
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (c : ι) (q : MvPolynomial (TVar d.D d.N) K) :
    d.sH c q = algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N) (d.sHp c q) := by
  have e : d.sH c = (IsScalarTower.toAlgHom K (MvPolynomial (SVar d.D d.N) (Ω c))
      (OmS (Ω c) d.D d.N)).comp (d.sHp c) := by
    apply MvPolynomial.algHom_ext
    intro p
    rw [AlgHom.comp_apply, sHp, MvPolynomial.aeval_X, IsScalarTower.coe_toAlgHom', sH, sHom,
      MvPolynomial.aeval_X]
    rfl
  rw [e]
  rfl
end ReciprocityTheory.ChartRestriction.G.T0.Data
