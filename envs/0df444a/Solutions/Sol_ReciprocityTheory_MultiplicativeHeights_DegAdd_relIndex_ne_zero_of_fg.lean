-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.DegAdd.relIndex_ne_zero_of_fg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:57:36.430642+00:00
-- url     : https://prove2.me/submissions/d4226cc0-2297-43d0-be25-146e7e300f7b

import Definitions.Def_ReciprocityTheory_SemistableReduction_LatSemiSt
import Definitions.Def_Lemmata_GeneralBFactBisAlt_Imports
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExistsIntSmulMemSpan
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_DegAdd_exists_int_smul_mem_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open ReciprocityTheory.MultiplicativeHeights.DegAdd
open NumberField
namespace ReciprocityTheory.MultiplicativeHeights.DegAdd
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r n : ℕ}
    (L : Submodule (𝓞 K) (Fin r → K)) (hL : L.FG) (v : Fin n → Fin r → K)
    (hv : ∀ x ∈ L, x ∈ Submodule.span K (Set.range v)) :
    (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex L.toAddSubgroup ≠ 0 := by
  set N := (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.addSubgroupOf L.toAddSubgroup
  have : Module.Finite (𝓞 K) L := Module.Finite.iff_fg.mpr hL
  have : Module.Finite ℤ L := Module.Finite.trans (𝓞 K) L
  let f : L →+ (L.toAddSubgroup ⧸ N) :=
    { toFun := fun x => QuotientAddGroup.mk (⟨x.1, x.2⟩ : L.toAddSubgroup)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have : Module.Finite ℤ (L.toAddSubgroup ⧸ N) := by
    refine Module.Finite.of_surjective f.toIntLinearMap ?_
    intro q
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact ⟨⟨y, hy⟩, rfl⟩
  have : Finite (L.toAddSubgroup ⧸ N) := by
    apply Module.finite_of_fg_torsion
    intro q
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨d, hd, hdy⟩ := exists_int_smul_mem_span v (hv y hy)
    refine ⟨⟨d, mem_nonZeroDivisors_of_ne_zero hd⟩, ?_⟩
    change (d • (QuotientAddGroup.mk (⟨y, hy⟩ : L.toAddSubgroup) : L.toAddSubgroup ⧸ N)) = 0
    rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    simpa using hdy
  exact AddSubgroup.index_ne_zero_of_finite
end ReciprocityTheory.MultiplicativeHeights.DegAdd
