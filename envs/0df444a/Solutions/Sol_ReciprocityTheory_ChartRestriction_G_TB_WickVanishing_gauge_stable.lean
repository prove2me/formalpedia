-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gauge_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:10:50.806311+00:00
-- url     : https://prove2.me/submissions/161de8b0-9cba-4a88-8184-3fef226d4cf2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HStable
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_M_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Finsupp
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
  {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution : ReciprocityTheory.ChartRestriction.G.TB.HStableSt := by
  intro R _ d O _ _ k _ _ _ _ B h hc a ξ hξ
  obtain ⟨u, φ, rfl⟩ := hξ
  have hA : ∀ (b : O) (i j : Fin d),
      dAct k B b i j = algebraMap R k (coeff (single ((0 : Fin 1), j) 1) (B.A.act b i)) := fun b i j => by
    unfold dAct FB.actK; rw [coeff_map]
  choose M hM using fun i j => M_int B h hc a i j
  set S := sg1 k h
  set vu : Fin d → k := fun j => algebraMap R k (u j)
  set vφ : Fin d → k := fun j => algebraMap R k (φ j)
  let u₂ : Fin d → R := fun i => ∑ j, coeff (single ((0 : Fin 1), j) 1) (B.A.act a i) * u j
  let φ₂ : Fin d → R := fun i => ∑ j, coeff (single ((0 : Fin 1), i) 1) (B.A.act (star a) j) * φ j + ∑ j, M i j * u j
  have hu₂ : (fun i => algebraMap R k (u₂ i)) = (dAct k B a).mulVec vu := funext fun i => by
    simp only [u₂, map_sum, map_mul, Matrix.mulVec, dotProduct, hA, vu]
  have hφ₂ : (fun i => algebraMap R k (φ₂ i)) = (dAct k B (star a)).transpose.mulVec vφ +
      (S * dAct k B a - (dAct k B (star a)).transpose * S).mulVec vu := funext fun i => by
    simp only [φ₂, map_add, map_sum, map_mul, Matrix.mulVec, dotProduct, hA, hM, Matrix.transpose_apply,
      Pi.add_apply, vu, vφ]
  refine ⟨u₂, φ₂, Prod.ext ?_ ?_⟩
  · exact hu₂.symm
  · show (dAct k B (star a)).transpose.mulVec (fun i => vφ i - S.mulVec vu i) =
      fun i => algebraMap R k (φ₂ i) - S.mulVec (fun j => algebraMap R k (u₂ j)) i
    rw [hu₂]
    have hφi : ∀ i, algebraMap R k (φ₂ i) = ((dAct k B (star a)).transpose.mulVec vφ +
        (S * dAct k B a - (dAct k B (star a)).transpose * S).mulVec vu) i := fun i => congrFun hφ₂ i
    simp only [hφi]
    have e1 : (fun i => vφ i - S.mulVec vu i) = vφ - S.mulVec vu := rfl
    rw [e1, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.mulVec_mulVec]
    funext i
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
