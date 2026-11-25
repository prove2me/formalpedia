-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.ED.free_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:59:58.586797+00:00
-- url     : https://prove2.me/submissions/7f29fe6c-1dca-4a66-ad8e-5ed690d53ee0

import Definitions.Def_ReciprocityTheory_DualLattices_DotSingle
import Definitions.Def_ReciprocityTheory_DualLattices_EmbeddingSeparatingGroupStatement
import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLengthOfLengthEigenLengthProduct
import Definitions.Def_ReciprocityTheory_DualLattices_EigenLengthProductStatementHolds
import Definitions.Def_ReciprocityTheory_DualLattices_ElementaryDivisorStatement
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_isLocal_of_integers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt



set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
open ReciprocityTheory.PGsh.Up.ED
variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]
namespace ReciprocityTheory.PGsh.Up.ED
theorem _root_.solution (hv : v.Integers R) {α : Type} [Fintype α] (S : Submodule R (α → R)) (hS : S.FG) :
    Module.Free R S ∧ Module.Finite R S := by
  haveI := isLocal_of_integers hv
  haveI : IsDomain R := Function.Injective.isDomain (algebraMap R C) hv.hom_inj
  haveI : ValuationRing R := ValuationRing.of_integers v hv
  haveI hfin : Module.Finite R S := Module.Finite.iff_fg.2 hS

  have htor : Submodule.torsion R S = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_torsion_iff] at hx
    obtain ⟨a, ha⟩ := hx
    rw [Submodule.mem_bot]
    apply Subtype.ext
    funext i
    have h1 : (a : R) * (x : α → R) i = 0 := by
      have := congrArg (fun y : S => (y : α → R) i) ha
      simpa [Submonoid.smul_def] using this
    have ha0 : (a : R) ≠ 0 := nonZeroDivisors.coe_ne_zero a
    simpa [ha0] using h1
  haveI : Module.Flat R S := (Module.Flat.flat_iff_torsion_eq_bot_of_isBezout).2 htor
  exact ⟨Module.free_of_flat_of_isLocalRing, hfin⟩
end ReciprocityTheory.PGsh.Up.ED
