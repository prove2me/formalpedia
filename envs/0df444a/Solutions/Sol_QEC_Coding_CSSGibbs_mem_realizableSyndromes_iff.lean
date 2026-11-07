-- Prove2me | solution 1 for QEC.Coding.CSSGibbs.mem_realizableSyndromes_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:06:31.505167+00:00
-- url     : https://prove2.me/submissions/a2909857-f840-4d8c-9876-62ddb3a1203f

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Projectors
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Spectrum

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.CSSGibbs
open Classical PauliSymplectic StabilizerCode Semantics
open scoped BigOperators
variable {ι κP κQ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κP] [Fintype κQ] [DecidableEq κP] [DecidableEq κQ]
variable (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
  (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
  (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
attribute [local instance] QEC.Coding.CSSGibbs._p2m_local_instance_ea4515a18e_14
attribute [local instance] QEC.Coding.CSSGibbs._p2m_local_instance_ea4515a18e_15
namespace QEC.Coding.CSSGibbs
theorem _root_.solution (s : Word (ZMod 2) (Sum κP κQ)) :
    s ∈ realizableSyndromes P Q ↔
      (fun p => s (.inl p)) ∈ LinearMap.range P ∧
      (fun q => s (.inr q)) ∈ LinearMap.range Q := by
  constructor
  · intro hs
    rcases Finset.mem_map.mp hs with ⟨⟨u,v⟩, _, rfl⟩
    exact ⟨u.property, v.property⟩
  · rintro ⟨hu,hv⟩
    apply Finset.mem_map.mpr
    refine ⟨(⟨_,hu⟩,⟨_,hv⟩), Finset.mem_univ _, ?_⟩
    funext j; cases j <;> rfl
end QEC.Coding.CSSGibbs
