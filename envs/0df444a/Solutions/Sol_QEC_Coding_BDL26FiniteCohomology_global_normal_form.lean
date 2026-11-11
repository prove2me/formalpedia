-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteCohomology.global_normal_form
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T09:59:45.367758+00:00
-- url     : https://prove2.me/submissions/c426dccc-eadc-412e-b1ee-56fe368e4069

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_class_normal_form
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26FiniteCohomology
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26AlternatingCochain
open BDL26ReplacementCochainMaps BDL26RZMap1CoordinateBridge
open BDL26IndexedDecoder MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26FiniteCohomology
theorem _root_.solution (S : OddScale) (n : Nat) (v : Cocycle S n) :
    ∃ f : Word Field (state S n).presentation.X,
      v.1 = tannerCoboundary0 (state S n).presentation f +
        (generator S n (finiteH1Equiv S n (classOf S n v))).1 := by
  let g := generator S n (finiteH1Equiv S n (classOf S n v))
  have hg : classOf S n v = classOf S n g := class_normal_form S n v
  have hz : classOf S n (v-g) = 0 := by
    rw [map_sub, hg, sub_self]
  have hb := (Submodule.Quotient.mk_eq_zero (complex S n).middleCoboundaryInCocycles).mp hz
  change v.1 - g.1 ∈ (complex S n).firstCoboundaryCheckCode.carrier at hb
  obtain ⟨f,hf⟩ := (BDL26RZCohomology.mem_boundary_iff (state S n).presentation _).mp hb
  refine ⟨f, ?_⟩
  funext q
  calc
    v.1 q = (v.1 q - g.1 q) + g.1 q := (sub_add_cancel _ _).symm
    _ = tannerCoboundary0 (state S n).presentation f q + g.1 q :=
      congrArg (fun a => a + g.1 q) (congrFun hf q).symm
end QEC.Coding.BDL26FiniteCohomology
