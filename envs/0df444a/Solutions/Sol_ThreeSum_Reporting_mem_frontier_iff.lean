-- Prove2me | solution 1 for ThreeSum.Reporting.mem_frontier_iff
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:00:48.460039+00:00
-- url     : https://prove2.me/submissions/8eb8c722-d194-4516-b152-9217e3fed0fb

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

section


/-!
# Executable positive-prefix reporting

The routine enumerates children of the current positive frontier and discards
zero counts. Its correctness interface asks for exact natural prefix counts;
the subset-transform identities supply those counts in the application.
No bound on the cost of obtaining a count is assumed or proved here.
-/

namespace ThreeSum.Reporting

open Finset
open scoped BigOperators

variable {ι α : Type*} [DecidableEq α]





theorem mass_pos_iff (I : Finset ι) (word : ι → List α) (weight : ι → ℕ)
    (k : ℕ) (pre : List α) :
    0 < mass I word weight k pre ↔
      ∃ i ∈ I, (word i).take k = pre ∧ 0 < weight i := by
  unfold mass Subset.fiberMass
  rw [Finset.sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
  simp only [mem_filter]
  constructor
  · rintro ⟨i, ⟨hi, hpre⟩, hw⟩
    exact ⟨i, hi, hpre, hw⟩
  · rintro ⟨i, hi, hpre, hw⟩
    exact ⟨i, ⟨hi, hpre⟩, hw⟩
























theorem mem_frontier_iff_sourceProof (I : Finset ι) (word : ι → List α) (weight : ι → ℕ)
    (children : ℕ → List α) (query : ℕ → List α → ℕ) (J k : ℕ)
    (hlen : ∀ i ∈ I, (word i).length = J)
    (hchildren : ∀ i (hi : i ∈ I), ∀ j (hj : j < J),
      (word i)[j]'(by rw [hlen i hi]; exact hj) ∈ children j)
    (hquery : ∀ j ≤ J, ∀ pre, query j pre = mass I word weight j pre)
    (hk : k ≤ J) (pre : List α) :
    pre ∈ frontier children query k ↔ 0 < mass I word weight k pre := by
  induction k generalizing pre with
  | zero =>
      constructor
      · intro hp
        simp only [frontier] at hp
        split at hp
        · have heq := List.mem_singleton.mp hp
          subst pre
          simpa only [hquery 0 (by omega) []] using ‹0 < query 0 []›
        · cases hp
      · intro hm
        obtain ⟨i, hi, hpre, hw⟩ := (mass_pos_iff I word weight 0 pre).mp hm
        have heq : pre = [] := by simpa using hpre.symm
        rw [heq] at hm ⊢
        simp [frontier, hquery 0 (by omega) [], hm]
  | succ k ih =>
      constructor
      · intro hp
        have hpos := (List.mem_filter.mp hp).2
        simpa only [decide_eq_true_eq, hquery (k + 1) hk pre] using hpos
      · intro hm
        obtain ⟨i, hi, hpre, hw⟩ := (mass_pos_iff I word weight (k + 1) pre).mp hm
        have hj : k < J := by omega
        have hlenk : k < (word i).length := by rw [hlen i hi]; exact hj
        have hparentMass : 0 < mass I word weight k ((word i).take k) :=
          (mass_pos_iff I word weight k _).mpr ⟨i, hi, rfl, hw⟩
        have hparent := (ih (by omega) ((word i).take k)).mpr hparentMass
        apply List.mem_filter.mpr
        constructor
        · apply List.mem_flatMap.mpr
          refine ⟨(word i).take k, hparent, ?_⟩
          apply List.mem_map.mpr
          exact ⟨(word i)[k], hchildren i hi k hj,
            (List.take_append_getElem hlenk).trans hpre⟩
        · simpa only [decide_eq_true_eq, hquery (k + 1) hk pre] using hm



























































end ThreeSum.Reporting

end

universe u_1 u_2

theorem solution : ∀ {ι : Type u_1} {α : Type u_2} [inst : DecidableEq.{u_2 + 1} α] (I : Finset.{u_1} ι) (word : ι → List.{u_2} α)
  (weight : ι → Nat) (children : Nat → List.{u_2} α) (query : Nat → List.{u_2} α → Nat) (J k : Nat)
  (hlen :
    ∀ (i : ι),
      @Membership.mem.{u_1, u_1} ι (Finset.{u_1} ι)
          (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} ι) ι (@Finset.instSetLike.{u_1} ι)) I i →
        @Eq.{1} Nat (@List.length.{u_2} α (word i)) J),
  (∀ (i : ι)
      (hi :
        @Membership.mem.{u_1, u_1} ι (Finset.{u_1} ι)
          (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} ι) ι (@Finset.instSetLike.{u_1} ι)) I i)
      (j : Nat) (hj : @LT.lt.{0} Nat instLTNat j J),
      @Membership.mem.{u_2, u_2} α (List.{u_2} α) (@List.instMembership.{u_2} α) (children j)
        (@GetElem.getElem.{u_2, 0, u_2} (List.{u_2} α) Nat α
          (fun (as : List.{u_2} α) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{u_2} α as))
          (@List.instGetElemNatLtLength.{u_2} α) (word i) j
          (@Eq.mpr.{0} (@LT.lt.{0} Nat instLTNat j (@List.length.{u_2} α (word i))) (@LT.lt.{0} Nat instLTNat j J)
            (@id.{0}
              (@Eq.{1} Prop (@LT.lt.{0} Nat instLTNat j (@List.length.{u_2} α (word i))) (@LT.lt.{0} Nat instLTNat j J))
              (@congrArg.{1, 1} Nat Prop (@List.length.{u_2} α (word i)) J
                (fun (_a : Nat) => @LT.lt.{0} Nat instLTNat j _a) (hlen i hi)))
            hj))) →
    (∀ (j : Nat),
        @LE.le.{0} Nat instLENat j J →
          ∀ (pre : List.{u_2} α),
            @Eq.{1} Nat (query j pre) (@ThreeSum.Reporting.mass.{u_1, u_2} ι α inst I word weight j pre)) →
      @LE.le.{0} Nat instLENat k J →
        ∀ (pre : List.{u_2} α),
          Iff
            (@Membership.mem.{u_2, u_2} (List.{u_2} α) (List.{u_2} (List.{u_2} α))
              (@List.instMembership.{u_2} (List.{u_2} α)) (@ThreeSum.Reporting.frontier.{u_2} α children query k) pre)
            (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@ThreeSum.Reporting.mass.{u_1, u_2} ι α inst I word weight k pre)) := by
  exact @ThreeSum.Reporting.mem_frontier_iff_sourceProof

#print axioms solution
