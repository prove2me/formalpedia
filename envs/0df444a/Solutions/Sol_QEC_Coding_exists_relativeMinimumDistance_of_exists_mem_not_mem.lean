-- Prove2me | solution 1 for QEC.Coding.exists_relativeMinimumDistance_of_exists_mem_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T18:13:56.674073+00:00
-- url     : https://prove2.me/submissions/b70f2e54-bc1a-47c3-89e5-fbc29414f0c2

-- ID: d2b28eaf-5dcb-4784-89d7-8edb548426f0 | NAME: QEC.Coding.exists_relativeMinimumDistance_of_exists_mem_not_mem | 未本地编译验证
import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Coding_Core_Definitions
set_option autoImplicit false
open QEC
open QEC.Coding
universe u v w x

theorem solution
    {F : Type u} {ι : Type v} [Field F] [Fintype F] [DecidableEq F] [Fintype ι]
    (ambient trivial : LinearCode F ι) (_hsub : trivial.carrier ≤ ambient.carrier)
    (hne : ∃ x : Word F ι, x ∈ ambient.carrier ∧ x ∉ trivial.carrier) :
    ∃ d : Nat, RelativeMinimumDistance ambient trivial d := by
  classical
  let P : Nat → Prop := fun d =>
    ∃ x : Word F ι, x ∈ ambient.carrier ∧ x ∉ trivial.carrier ∧ HammingWeight x = d
  have hP : ∃ d, P d := by
    rcases hne with ⟨x, hxA, hxT⟩
    exact ⟨HammingWeight x, x, hxA, hxT, rfl⟩
  let d := Nat.find hP
  have hd : P d := Nat.find_spec hP
  rcases hd with ⟨x, hxA, hxT, hxw⟩
  refine ⟨d, x, hxA, hxT, hxw, ?_⟩
  intro y hyA hyT
  exact Nat.find_min' hP ⟨y, hyA, hyT, rfl⟩
