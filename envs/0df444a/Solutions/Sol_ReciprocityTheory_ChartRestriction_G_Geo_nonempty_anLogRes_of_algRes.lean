-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.nonempty_anLogRes_of_algRes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:15:54.232147+00:00
-- url     : https://prove2.me/submissions/0a1acb24-0562-4b58-ae1b-6fff926a511c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterPC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsAtlas
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_SNCstep
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_Immersion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterAlgRes
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_mem_mcPts_iff_conePts_pC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_sameOrbit_trans
import Theorems.Thm_ReciprocityTheory_AnForm_R_AlgRes_exists_atlas
import Theorems.Thm_ReciprocityTheory_AnForm_R_AlgRes_fderiv_affCoord_ker_eq_bot
import Theorems.Thm_ReciprocityTheory_AnForm_R_AlgRes_isSNC_pullback
import Theorems.Thm_ReciprocityTheory_AnForm_R_AlgRes_volume_preimage_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial ReciprocityTheory.AnForm.M
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (P J : Ideal (MRing ι)) (e : ℕ)
    (hJ : IsMultiHomogIdeal J) (hJP : ¬ J ≤ P)
    (hPC : ∀ f : MRing ι, MvPolynomial.map (Int.castRingHom ℂ) f ∈ pC P → f ∈ P)
    (R : ReciprocityTheory.AnForm.R.AlgRes ι (pC P) (pC J) e) : Nonempty (AnLogRes P J e) := by
  classical
  obtain ⟨A, hA⟩ := R.exists_atlas
  choose idx hidx using R.cover
  refine ⟨{
    homog := hJ
    nondeg := hJP
    X := R.M
    A := A
    U := fun x => R.src (idx x)
    isOpen_U := fun x => R.isOpen_alt_bis (idx x)
    mem_U := hidx
    lift := fun x y q => eval (R.coord (idx x) y) (R.lift (idx x) q)
    holo := fun x p => hA.1 (idx x) (R.lift (idx x) p)
    mem := ?_
    compat := ?_
    surj := ?_
    inj := ?_
    immersion := ?_
    snc := ?_
    null := ?_ }⟩
  · intro x y hy
    rw [mem_mcPts_iff_conePts_pC]
    exact R.lift_mem (idx x) y hy
  · intro x x' y hy
    exact R.compat (idx x) (idx x') y hy
  · intro z hz hzJ
    rw [mem_mcPts_iff_conePts_pC] at hz hzJ
    obtain ⟨i, x, hx, hxz⟩ := R.surj z hz hzJ
    exact ⟨x, sameOrbit_trans (R.compat (idx x) i x ⟨hidx x, hx⟩) hxz⟩
  · intro x x' hxJ hxx
    rw [mem_mcPts_iff_conePts_pC] at hxJ
    exact R.inj (idx x) (idx x') x (hidx x) x' (hidx x') hxJ hxx
  · intro x hxJ p hp j hj
    rw [mem_mcPts_iff_conePts_pC] at hxJ
    exact R.fderiv_affCoord_ker_eq_bot A hA (idx x) x (hidx x) hxJ p hp j hj
  · intro f a hfP hf hz
    have hf' : ReciprocityTheory.AnForm.R.IsMultiHomog (map (Int.castRingHom ℂ) f) a :=
      fun m hm k => hf m (support_map_subset _ _ hm) k
    have hfP' : map (Int.castRingHom ℂ) f ∉ pC P := fun h => hfP (hPC f h)
    have hz' : ∀ z ∈ ReciprocityTheory.AnForm.R.conePts (pC P), eval z (map (Int.castRingHom ℂ) f) = 0 →
        z ∈ ReciprocityTheory.AnForm.R.conePts (pC J) := by
      intro z hz1 hz2
      rw [← mem_mcPts_iff_conePts_pC] at hz1 ⊢
      exact hz z hz1 hz2
    obtain ⟨m, hm⟩ := R.isSNC_pullback A hA idx hidx (fun _ _ => 0) _ a hf' hfP' hz'
    exact ⟨R.rc, m, R.comp, hm⟩
  · intro j
    refine MeasureTheory.measure_mono_null ?_ (R.volume_preimage_eq_zero A hA j)
    rintro y ⟨hy1, hy2⟩
    refine ⟨hy1, idx _, hidx _, ?_⟩
    simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hy2 ⊢
    rw [← mem_mcPts_iff_conePts_pC]
    exact hy2
end ReciprocityTheory.ChartRestriction.G.Geo
