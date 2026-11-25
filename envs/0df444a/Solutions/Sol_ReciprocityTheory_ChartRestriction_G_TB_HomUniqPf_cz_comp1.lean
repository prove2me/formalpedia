-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.HomUniqPf.cz_comp1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:52:32.157657+00:00
-- url     : https://prove2.me/submissions/cf92b404-7597-4fd5-9188-bbfa2047b35a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_PderivSecondEvFirstPointEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ConstantCoeffEv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HomUniq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_HomUniqPf_cz1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_cz1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
namespace ReciprocityTheory.ChartRestriction.G.TB
namespace HomUniqPf
open ReciprocityTheory.ChartRestriction.G.TB.LogPf Formalism.FG.SolveVAux
variable {k : Type} [CommRing k] {d : ℕ}
private theorem cc_ev_lemma {m n : ℕ} {a : Fin m → Pt k n d} (ha : CZ a) (f : PS k m d) :
    constantCoeff (ev a f) = constantCoeff f := by
  unfold ev
  have hs : MvPowerSeries.HasSubst (fun p : Fin m × Fin d => a p.1 p.2) := by
    first
      | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => ha p.1 p.2)
      | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent
          (fun p => by rw [ha p.1 p.2]; exact IsNilpotent.zero)
  rw [MvPowerSeries.constantCoeff_subst hs, finsum_eq_single _ 0]
  · simp
  · intro e he
    obtain ⟨s, hs'⟩ : ∃ s, e s ≠ 0 := by
      by_contra h
      push_neg at h
      exact he (Finsupp.ext h)
    rw [Finsupp.prod, map_prod, Finset.prod_eq_zero (i := s) (Finsupp.mem_support_iff.mpr hs'),
      smul_zero]
    rw [map_pow, ha s.1 s.2, zero_pow hs']
end HomUniqPf
end ReciprocityTheory.ChartRestriction.G.TB
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB
open ReciprocityTheory.ChartRestriction.G.TB.HomUniqPf
open ReciprocityTheory.ChartRestriction.G.TB.LogPf Formalism.FG.SolveVAux
variable {k : Type} [CommRing k] {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.TB.HomUniqPf
theorem _root_.solution {n : ℕ} (φ : Pt k 1 d) (hφ : ∀ i, constantCoeff (φ i) = 0) (a : Pt k n d)
    (ha : ∀ i, constantCoeff (a i) = 0) : ∀ i, constantCoeff (comp1 φ a i) = 0 := by
  unfold comp1
  intro i
  rw [cc_ev_lemma (cz1 a ha), hφ i]
end ReciprocityTheory.ChartRestriction.G.TB.HomUniqPf
