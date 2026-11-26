-- Prove2me | solution 1 for Section5PowerCode.exists_binary_field_character
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:06:11.143875+00:00
-- url     : https://prove2.me/submissions/ec4632ea-27d2-478a-bf90-11701fdd1b58

import Definitions.Def_Section5Verified_Section5BinaryFieldCharacter
import Mathlib
section
set_option autoImplicit false

open Module

namespace Section5PowerCode







theorem basisCharacter_nontrivial {F α : Type*} [AddCommGroup F] [Module (ZMod 2) F]
    (b : Basis α (ZMod 2) F) (i : α) : basisCharacter b i ≠ 0 := by
  classical
  intro h
  have he := congrArg (fun ψ : AddChar F ℝ => ψ (b i)) h
  norm_num [basisCharacter,binaryCharacter,Basis.coord_apply,Basis.repr_self,
    ZMod.val_one_eq_one_mod] at he



end Section5PowerCode

end
set_option autoImplicit false
open Module
namespace Section5PowerCode
end Section5PowerCode
open Section5PowerCode
theorem solution {F : Type*} [Field F] [Algebra (ZMod 2) F] :
    ∃ χ : AddChar F ℝ, χ ≠ 0 := by
  let b := Module.Free.chooseBasis (ZMod 2) F
  have hne : Nonempty (Module.Free.ChooseBasisIndex (ZMod 2) F) :=
    b.index_nonempty
  exact ⟨Section5PowerCode.basisCharacter b (Classical.choice hne),
    Section5PowerCode.basisCharacter_nontrivial b (Classical.choice hne)⟩
