-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_subfield_closure_coords_eq_top_76055511fe92
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:05:27.43286+00:00
-- url     : https://prove2.me/submissions/c09dd95e-707a-413b-af42-09518865299c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsLocRingIntClosure
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StLocRingChartLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StIntClosureLocFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PLocRingIntClosure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter
open Classical
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι')) [P'.IsPrime] :
    Subfield.closure ((Finset.univ.image fun q : Σ k, ι' k =>
      algebraMap (MRing ι' ⧸ P') (FractionRing (MRing ι' ⧸ P')) (Ideal.Quotient.mk P' (X q)) :
        Finset (FractionRing (MRing ι' ⧸ P'))) : Set (FractionRing (MRing ι' ⧸ P'))) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := MRing ι' ⧸ P') x
  have h : ∀ f : MRing ι', algebraMap (MRing ι' ⧸ P') (FractionRing (MRing ι' ⧸ P')) (Ideal.Quotient.mk P' f) ∈
      Subfield.closure ((Finset.univ.image fun q : Σ k, ι' k =>
        algebraMap (MRing ι' ⧸ P') (FractionRing (MRing ι' ⧸ P')) (Ideal.Quotient.mk P' (X q)) :
          Finset (FractionRing (MRing ι' ⧸ P'))) : Set (FractionRing (MRing ι' ⧸ P'))) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C r => rw [eq_intCast C r, map_intCast, map_intCast]; exact intCast_mem _ r
    | add f g hf hg => rw [map_add, map_add]; exact add_mem hf hg
    | mul_X f q hf =>
      rw [map_mul, map_mul]
      exact mul_mem hf (Subfield.subset_closure (by simp))
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact div_mem (h f) (h g)
end GroundTheory.Heights₂.Heights.Inter
