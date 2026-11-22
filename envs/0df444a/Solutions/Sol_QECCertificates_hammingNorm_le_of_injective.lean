-- Prove2me | solution 1 for QECCertificates.hammingNorm_le_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:48:05.467932+00:00
-- url     : https://prove2.me/submissions/f54159ae-1633-46ac-b0ad-749cb23df38b

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCompression

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {r₁ n₁ r₂ n₂ : ℕ}
namespace QECCertificates
theorem _root_.solution {α β : Type*} [Fintype α] [Fintype β] (e : α → β)
    (he : Function.Injective e) (v : β → ZMod 2) :
    hammingNorm (fun a => v (e a)) ≤ hammingNorm v := by
  change (Finset.univ.filter (fun a => v (e a) ≠ 0)).card
    ≤ (Finset.univ.filter (fun b => v b ≠ 0)).card
  refine Finset.card_le_card_of_injOn e ?_ ?_
  · intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩
  · intro a _ b _ h
    exact he h
end QECCertificates
