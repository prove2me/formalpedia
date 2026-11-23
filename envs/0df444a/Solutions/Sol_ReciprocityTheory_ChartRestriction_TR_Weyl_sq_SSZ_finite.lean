-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.TR.Weyl.sq_SSZ_finite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:30:28.253257+00:00
-- url     : https://prove2.me/submissions/614e728c-5f59-46cf-bb2f-bfbc7f343fee

import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_AltBranchStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_SqCharA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.TR ReciprocityTheory.ChartRestriction.TR.Weyl
namespace ReciprocityTheory.ChartRestriction.TR.Weyl
theorem _root_.solution (k : ℕ) (κ : Fin k → ℤ) : Finite (sq_SSZ k κ) := by
  classical
  let B : ℕ := ∑ t, (κ t).toNat
  have hinj : Function.Injective (fun g : sq_SSZ k κ => fun a t => (⟨g.1 a t, by
      have h1 : g.1 a t ≤ ∑ a, g.1 a t :=
        Finset.single_le_sum (f := fun a => g.1 a t) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
      have h2 := g.2.2 t
      have h3 : (κ t).toNat ≤ B :=
        Finset.single_le_sum (f := fun t => (κ t).toNat) (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
      omega⟩ : Fin (B + 1))) := by
    intro g g' h
    apply Subtype.ext
    funext a t
    exact congrArg Fin.val (congrFun (congrFun h a) t)
  exact Finite.of_injective _ hinj
end ReciprocityTheory.ChartRestriction.TR.Weyl
