-- Prove2me | solution 1 for QEC.Coding.exists_algebraicCSSMinimumDistance_of_exists_logical
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T18:38:59.928112+00:00
-- url     : https://prove2.me/submissions/1d55e132-1fe2-43b2-993a-aeb652976343

-- ID: dd860299-b6ca-4dd9-a058-a18cff45f9f4 | NAME: QEC.Coding.exists_algebraicCSSMinimumDistance_of_exists_logical | 未本地编译验证
import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Coding_Core_Definitions
set_option autoImplicit false
open QEC
open QEC.Coding
universe u v w x

theorem solution
    {F : Type u} {ι : Type v} [Field F] [Fintype F]
    [DecidableEq F] [Fintype ι]
    (xCode zCode : LinearCode F ι)
    (hne : ∃ x : Word F ι,
      (x ∈ zCode.dual.carrier ∧ x ∉ xCode.carrier) ∨
        (x ∈ xCode.dual.carrier ∧ x ∉ zCode.carrier)) :
    ∃ d : Nat, AlgebraicCSSMinimumDistance xCode zCode d := by
  classical
  let P : Nat → Prop := fun d =>
    ∃ x : Word F ι,
      ((x ∈ zCode.dual.carrier ∧ x ∉ xCode.carrier) ∨
        (x ∈ xCode.dual.carrier ∧ x ∉ zCode.carrier)) ∧ HammingWeight x = d
  have hP : ∃ d, P d := by
    rcases hne with ⟨x, hx⟩
    exact ⟨HammingWeight x, x, hx, rfl⟩
  let d := Nat.find hP
  have hd : P d := Nat.find_spec hP
  rcases hd with ⟨x, hx, hxw⟩
  refine ⟨d, x, hx, hxw, ?_⟩
  intro y hy
  exact Nat.find_min' hP ⟨y, hy, rfl⟩
