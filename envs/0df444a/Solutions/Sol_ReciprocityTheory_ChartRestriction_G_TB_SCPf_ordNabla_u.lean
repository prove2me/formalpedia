-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.SCPf.ordNabla_u
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:32:38.554895+00:00
-- url     : https://prove2.me/submissions/32790ea6-9b33-414b-8df5-accb8f9361c3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondOrderIterateEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SCWick
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_nablaL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.TB.SCPf.nablaL_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.SCPf
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]
namespace ReciprocityTheory.ChartRestriction.G.TB.SCPf
theorem _root_.solution (hN2 : ConnectionCommutator) (B : FB R d O) (h : PS k 2 d) (m : ℕ) {ι : Type} [Fintype ι] (s : ι → Bool)
    (u : ι → Fin d → k) (P : MvPolynomial ι k) (G : AA k d) :
    ordNabla k B h m s (fun l => (u l, 0)) P G = nablaPoly k B h m u P G := by
  have hcomm : ∀ a b : ι, Function.Commute (nabla k B h m (u a) 0) (nabla k B h m (u b) 0) := by
    intro a b z
    have hz := hN2 R d O k B h m (u a, 0) (u b, 0) z
    have hb : betaH k (u a, (0 : Fin d → k)) (u b, 0) = 0 := by simp [betaH]
    rw [hb, mul_zero, map_zero, zero_mul] at hz
    exact sub_eq_zero.mp hz
  unfold ordNabla nablaPoly
  refine Finset.sum_congr rfl fun n _ => ?_
  congr 1
  rw [← List.foldr_append]
  refine List.Perm.foldr_eq' (List.filter_append_perm _ _) ?_ _
  intro x _ y _ z
  exact (hcomm y x).iterate_iterate (n y) (n x) z
end ReciprocityTheory.ChartRestriction.G.TB.SCPf
