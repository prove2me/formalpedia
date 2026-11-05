-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativeTupleWitness.positional_ofFn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:35:41.471652+00:00
-- url     : https://prove2.me/submissions/320bb910-a42a-4590-8e3d-dde2d3069a41

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryRepeatedWords
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryGoodOutputCatalog
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeTupleWitness
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalNativeTupleWitness_positional_map
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalNativeTupleWitness_positional_cast_digits

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativeTupleWitness
open Finset TernaryJointType WeightedGlobalLocalParameters TernaryCoverLocal WeightedGlobalCoverGoodMaps
open WeightedGlobalNativeCoverWitness TernaryExtensionEncoding TernaryFixedDictionaries
open scoped BigOperators
variable {p m : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativeTupleWitness
theorem _root_.solution {A : Type*} {r : ℕ} (xs : Fin r → A) (raw : A → ℤ)
    (v : Fin r → ZMod p) (hraw : ∀ i, raw (xs i)=(v i).val) :
    Radix.positionalHash (p : ℤ) raw (List.ofFn xs)=(coefficientCode v : ℤ) := by
  have h1 : (List.ofFn xs).map raw=List.ofFn (fun i => ((v i).val : ℤ)) := by
    rw [List.map_ofFn]
    apply List.ofFn_inj.mpr
    funext i
    exact hraw i
  have h2 : (List.ofFn fun i => (v i).val).map (fun a : ℕ => (a : ℤ))=
      List.ofFn (fun i => ((v i).val : ℤ)) := List.map_ofFn
  calc
    _ = Radix.positionalHash (p : ℤ) id ((List.ofFn xs).map raw) := positional_map _ _ _ _
    _ = Radix.positionalHash (p : ℤ) id
        ((List.ofFn fun i => (v i).val).map (fun a : ℕ => (a : ℤ))) := by rw [h1,h2]
    _ = Radix.positionalHash (p : ℤ) (fun a : ℕ => (a : ℤ)) (List.ofFn fun i => (v i).val) :=
      (positional_map _ _ _ _).symm
    _ = _ := positional_cast_digits p _
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativeTupleWitness
