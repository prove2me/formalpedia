-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.lenEx
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:34:18.613897+00:00
-- url     : https://prove2.me/submissions/88f63f5e-c179-4807-93c9-6bcf4acf5b50

import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLowerBoundOf
import Definitions.Def_ReciprocityTheory_DualLattices_UpSmith
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsSmulMemOfMemSpan
import Definitions.Def_ReciprocityTheory_DualLattices_LenEx
import Theorems.Thm_ReciprocityTheory_PGsh_L2_SecondCohomologyLattice_free_of_finite_torsionFree


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution : LenExStatement := by
  intro C _ v R _ _ hv g Ht A B
  classical
  have : IsDomain R := hv.hom_inj.isDomain
  have := ValuationRing.of_integers v hv
  set Mm := LinearMap.range (Matrix.mulVecLin Aᵀ) with hMm
  set N := (LinearMap.range (Matrix.mulVecLin B)).map (Matrix.mulVecLin Ht) with hN
  have hfgM : Mm.FG := by
    rw [hMm, LinearMap.range_eq_map]; exact Module.Finite.fg_top.map _
  have hfgN : N.FG := by
    rw [hN, LinearMap.range_eq_map]; exact (Module.Finite.fg_top.map _).map _
  set S := Mm ⊔ N with hS
  have hfgS : S.FG := hfgM.sup hfgN
  have : Module.Finite R S := Module.Finite.iff_fg.2 hfgS
  have : Module.Free R S := L2.SecondCohomologyLattice.free_of_finite_torsionFree S (by
    rintro r ⟨x, hx⟩ hr h
    apply Subtype.ext
    funext i
    have := congrFun (congrArg Subtype.val h) i
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Submodule.coe_zero,
      Pi.zero_apply] at this
    exact (mul_eq_zero.1 this).resolve_left hr)
  set bS := (Module.Free.chooseBasis R S).reindex (Fintype.equivFin _) with hbS
  set e := bS.equivFun with he
  set N' := N.comap S.subtype with hN'
  have hfgN' : N'.FG := by
    apply Submodule.fg_of_fg_map_injective S.subtype S.injective_subtype
    rw [hN', Submodule.map_comap_subtype, inf_eq_right.2 le_sup_right]
    exact hfgN
  set K := N'.map e.toLinearMap with hK
  have hfgK : K.FG := hfgN'.map _
  obtain ⟨n, gK, hgK⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hfgK
  obtain ⟨c, ⟨ec⟩⟩ := Smith.smith_gen hv _ gK
  refine ⟨∏ i, v (algebraMap R C (c i)), _, c, ⟨?_⟩, rfl⟩
  have h1 : N.comap Mm.subtype = Mm.comap Mm.subtype ⊓ N.comap Mm.subtype := by
    rw [Submodule.comap_subtype_self, top_inf_eq]
  exact (Submodule.quotEquivOfEq _ _ h1).trans ((LinearMap.quotientInfEquivSupQuotient Mm N).trans
    ((Submodule.Quotient.equiv N' K e rfl).trans ((Submodule.quotEquivOfEq _ _ hgK.symm).trans ec)))
end ReciprocityTheory.PGsh.Up
