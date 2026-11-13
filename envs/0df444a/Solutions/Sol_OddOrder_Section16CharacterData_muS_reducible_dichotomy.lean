-- Prove2me | solution 1 for OddOrder.Section16CharacterData.muS_reducible_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T17:47:12.55033+00:00
-- url     : https://prove2.me/submissions/86a5e45c-77ba-450d-9fee-ad93eb91c5fe

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/FeitThompsonSetup.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_FeitThompsonSetup

-- ===== OddOrder/FeitThompsonSetup.lean =====
namespace OddOrder

open OddOrder.BG

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.RepresentationTheory

open scoped Pointwise

universe u

section

open scoped OddOrder.Peterfalvi.S15.FiniteInduce

namespace Section16CharacterData

variable {G : Type*} [Group G] [Finite G] (hG : IsMinimalSimpleOdd G) (mp : Section16MaximalPair G)

variable (tp : Section16TypePStructure mp)

variable [NeZero (Nat.card ↥(mp.certainTypeS hG).W1)]

set_option backward.isDefEq.respectTransparency false in
/-- **Peterfalvi (9.8)/(9.11) reverse dichotomy at the `S`-instance certain-type grid** — the
producer supply for the `mu_reducible_dichotomy` field (issue 9092).  A *reducible* member of the
kernel-filter family `S(X)` over `S' = (derivedInG mp.S).subgroupOf mp.S` (any kernel demand `X`)
is a nonzero `μ`-column sum `∑ᵢ μ_{ij}`, `j ≠ 0`.  Mirrors the M-side
`Hypothesis.reducible_mem_inducedKernelFamily_eq_muGrid_columnSum` (`S12_HcBound`) at
`mp.certainTypeS hG`, using the identification `μ = columnFamily.mu` (`muS`) and the §6
reducibility criterion `induce_not_isIrreducible_iff` (the reducible source `θ = Ind_{S'}` is one
of the certain-type columns `χ_{j}`, whose column enumeration `chi2enum` supplies the `j`). -/
theorem _root_.solution {X : Subgroup ↥mp.S} {ψ : ClassFunction ↥mp.S ℂ}
    (hψ : ψ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG mp.S).subgroupOf mp.S) X)
    (hred : ¬ OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ) :
    ∃ j : Fin tp.p, j ≠ ⟨0, tp.p_prime.pos⟩ ∧ ψ = ∑ i : Fin tp.q, muS hG mp tp i j := by
  classical
  have hcyc : IsCyclic ↥((mp.certainTypeS hG).W1 ⊔ (mp.certainTypeS hG).W2) :=
    (mp.certainTypeS hG).isCyclic_sup
  let : CommGroup ↥((mp.certainTypeS hG).W1 ⊔ (mp.certainTypeS hG).W2) := IsCyclic.commGroup
  let : Fintype ↥mp.S := Fintype.ofFinite _
  let : Fintype ↥(mp.certainTypeS hG).K := Fintype.ofFinite _
  let : Fintype ↥((mp.certainTypeS hG).W1 ⊔ (mp.certainTypeS hG).W2) := Fintype.ofFinite _
  obtain ⟨θ, hθne, hθker, rfl⟩ := hψ
  -- the μ-column sum is `Ind_{S'} χ_j` (reversing the `mu_colSum_eq_induce` identity)
  have hFk : ∀ j : Fin tp.p, (∑ i : Fin tp.q, muS hG mp tp i j)
      = ClassFunction.induce (mp.certainTypeS hG).K
          (((mp.certainTypeS hG).chiRestrict (chi2enum hG mp tp j) :
            ClassFunction ↥(mp.certainTypeS hG).K ℂ)) := by
    intro j
    rw [(mp.certainTypeS hG).coe_chiRestrict, (mp.certainTypeS hG).induce_restrict_certainType_eq]
    simp only [muS]
    exact Equiv.sum_comp (eqQ hG mp tp)
      (fun i' => (((mp.certainTypeS hG).columnFamily (chi2enum hG mp tp j)).mu i'
        : ClassFunction ↥mp.S ℂ))
  -- the reducible source `θ` is a §6 column `χ_j`
  obtain ⟨χ₂', hχ₂'⟩ := ((mp.certainTypeS hG).induce_not_isIrreducible_iff θ).mp hred
  have hχ₂'ne : χ₂' ≠ 1 := by
    rintro rfl
    rw [(mp.certainTypeS hG).chiRestrict_one_eq_trivial] at hχ₂'
    exact hθne hχ₂'.symm
  refine ⟨(chi2enum hG mp tp).symm χ₂', ?_, ?_⟩
  · intro h0
    apply hχ₂'ne
    calc χ₂' = chi2enum hG mp tp ((chi2enum hG mp tp).symm χ₂') :=
          (Equiv.apply_symm_apply _ _).symm
      _ = chi2enum hG mp tp ⟨0, tp.p_prime.pos⟩ := by rw [h0]
      _ = 1 := chi2enum_zero hG mp tp
  · rw [hFk, Equiv.apply_symm_apply, hχ₂']
    -- `(mp.certainTypeS hG).K` is defeq `(derivedInG mp.S).subgroupOf mp.S` (`certainTypeS_K_eq`)
    exact rfl

end Section16CharacterData

end

end OddOrder
