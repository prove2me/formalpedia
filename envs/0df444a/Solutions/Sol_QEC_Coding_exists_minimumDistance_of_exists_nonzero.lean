-- Prove2me | solution 1 for QEC.Coding.exists_minimumDistance_of_exists_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T18:38:59.834445+00:00
-- url     : https://prove2.me/submissions/65acda91-b206-4b39-9619-cd28d5878a89

-- ID: cfb37548-bfbe-4070-a310-16f7d8735637 | NAME: QEC.Coding.exists_minimumDistance_of_exists_nonzero | 未本地编译验证
import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Coding_Core_Definitions
set_option autoImplicit false
open QEC
open QEC.Coding
universe u v w x

theorem solution {F : Type u} {ι : Type v}
    [Field F] [Fintype F] [DecidableEq F] [Fintype ι] (C : LinearCode F ι)
    (hC : ∃ x : Word F ι, x ∈ C.carrier ∧ x ≠ 0) :
    ∃ d : Nat, MinimumDistance C d := by
  classical
  let P : Nat → Prop := fun d =>
    ∃ x : Word F ι, x ∈ C.carrier ∧ x ≠ 0 ∧ HammingWeight x = d
  have hP : ∃ d, P d := by
    rcases hC with ⟨x, hxC, hx0⟩
    exact ⟨HammingWeight x, x, hxC, hx0, rfl⟩
  let d := Nat.find hP
  have hd : P d := Nat.find_spec hP
  rcases hd with ⟨x, hxC, hx0, hxw⟩
  refine ⟨d, x, hxC, hx0, hxw, ?_⟩
  intro y hyC hy0
  exact Nat.find_min' hP ⟨y, hyC, hy0, rfl⟩
