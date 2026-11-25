-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.kirr_compact_word
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:26:22.473354+00:00
-- url     : https://prove2.me/submissions/7172fbd9-6d06-419e-b456-7dec3039103c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_KhwWeightEqOfIrr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_kirrWord_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_kirr_low_mem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
section KIrr
variable {X : Type*} [AddCommGroup X] [Module ℂ X] {ε : Fin n → Bool}
  {A : Fin n → Fin n → Module.End ℂ X} {Λ : Fin n → ℝ} {V : Submodule ℂ X}
private theorem glRep_apply_commutator (hA : IsGlRep A) (a b c d : Fin n) (v : X) :
    A a b (A c d v) = A c d (A a b v) + ((if b = c then A a d else 0) - if d = a then A c b else 0) v :=
  eq_add_of_sub_eq' (by
    have h := LinearMap.congr_fun (hA a b c d) v
    rw [LinearMap.sub_apply] at h
    exact h)
end KIrr
end ReciprocityTheory.ChartRestriction.DS
end
end

set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {X : Type*} [AddCommGroup X] [Module ℂ X] {ε : Fin n → Bool}
  {A : Fin n → Fin n → Module.End ℂ X} {Λ : Fin n → ℝ} {V : Submodule ℂ X}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hA : IsGlRep A) {ν : Fin n → ℝ} {u : X} (hu : IsKHWVec ε A ν u) :
    ∀ l, KirrLow ε l → ∀ a b, ε a = ε b → A a b (kirrWord A u l) ∈ kirrSpan ε A u := by
  intro l
  induction l with
  | nil =>
    intro _ a b hab
    rcases lt_trichotomy a b with h | rfl | h
    · show A a b u ∈ _
      rw [hu.2 a b h hab]; exact Submodule.zero_mem _
    · show A a a u ∈ _
      rw [hu.1 a]
      exact Submodule.smul_mem _ _ (kirrWord_mem (l := []) u (fun p hp => by simp at hp))
    · exact kirrWord_mem (l := [(a, b)]) u (fun p hp => by
        rw [List.mem_singleton] at hp; subst hp; exact ⟨h, hab⟩)
  | cons p l ih =>
    intro hl a b hab
    obtain ⟨x, y⟩ := p
    have hl' : KirrLow ε l := fun q hq => hl q (List.mem_cons_of_mem _ hq)
    have hxy : y < x ∧ ε x = ε y := hl (x, y) (by simp)
    have hw := ih hl'
    show A a b (A x y (kirrWord A u l)) ∈ _
    rw [glRep_apply_commutator hA]
    refine Submodule.add_mem _ (kirr_low_mem hxy.1 hxy.2 (hw a b hab)) ?_
    rw [LinearMap.sub_apply]
    refine Submodule.sub_mem _ ?_ ?_
    · split_ifs with h
      · subst h; exact hw _ _ (hab.trans hxy.2)
      · rw [LinearMap.zero_apply]; exact Submodule.zero_mem _
    · split_ifs with h
      · subst h; exact hw _ _ (hxy.2.trans hab)
      · rw [LinearMap.zero_apply]; exact Submodule.zero_mem _
end ReciprocityTheory.ChartRestriction.DS
