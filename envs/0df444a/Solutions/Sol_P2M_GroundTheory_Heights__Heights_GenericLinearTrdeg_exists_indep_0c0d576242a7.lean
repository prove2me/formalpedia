-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GenericLinearTrdeg_exists_indep_0c0d576242a7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:25:18.367673+00:00
-- url     : https://prove2.me/submissions/8be3c6b7-5239-47e0-8dde-1d90cad8ce49

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PGenericLinearTrdeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open GroundTheory.Heights₂.Heights.GenericLinearTrdeg
namespace GroundTheory.Heights₂.Heights.GenericLinearTrdeg
theorem _root_.solution {F E : Type} [Field F] [Field E] [Algebra F E] {N : ℕ} (η : Fin N → E) (d : ℕ)
    (hd : Algebra.trdeg F (Algebra.adjoin F (Set.range η)) = d) :
    ∃ j : Fin d → Fin N, AlgebraicIndependent F (η ∘ j) := by
  classical
  set D := Algebra.adjoin F (Set.range η)
  let ηD : Fin N → D := fun m => ⟨η m, Algebra.subset_adjoin ⟨m, rfl⟩⟩
  have htop : Algebra.adjoin F (Set.range ηD) = ⊤ := by
    apply Subalgebra.map_injective (f := D.val) Subtype.val_injective
    rw [← Algebra.adjoin_image, Algebra.map_top, Subalgebra.range_val, ← Set.range_comp]
    rfl
  have : Algebra.IsAlgebraic (Algebra.adjoin F (Set.range ηD)) D :=
    ⟨fun y => isAlgebraic_algebraMap (R := Algebra.adjoin F (Set.range ηD))
      (⟨y, by rw [htop]; trivial⟩ : Algebra.adjoin F (Set.range ηD))⟩
  have : FaithfulSMul F D :=
    (faithfulSMul_iff_algebraMap_injective F D).mpr (algebraMap F D).injective
  obtain ⟨t, hts, hb⟩ := exists_isTranscendenceBasis_subset (R := F) (Set.range ηD)
  have hcard : Cardinal.mk t = d := hb.cardinalMk_eq_trdeg.trans hd
  have hfin : t.Finite := (Set.finite_range ηD).subset hts
  have := hfin.fintype
  have hc : Fintype.card t = d := by
    rw [Cardinal.mk_fintype] at hcard
    exact_mod_cast hcard
  let e : Fin d ≃ t := (Fintype.equivFinOfCardEq hc).symm
  have hpre : ∀ l, ∃ m, ηD m = (e l : D) := fun l => hts (e l).2
  choose j hj using hpre
  refine ⟨j, ?_⟩
  have h1 : AlgebraicIndependent F (fun l => ((e l : t) : D)) := hb.1.comp e e.injective
  have h2 := h1.map' (f := D.val) Subtype.val_injective
  convert h2 using 1
  funext l
  simp only [Function.comp_apply]
  rw [← hj l]
  rfl
end GroundTheory.Heights₂.Heights.GenericLinearTrdeg
