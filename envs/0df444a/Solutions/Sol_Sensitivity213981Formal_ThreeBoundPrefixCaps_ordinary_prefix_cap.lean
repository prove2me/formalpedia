-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundPrefixCaps.ordinary_prefix_cap
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T19:53:24.19299+00:00
-- url     : https://prove2.me/submissions/f14a99e4-d141-441e-8013-00116bbfa716

import Definitions.Def_Sensitivity213981Formal_ActualPrefixCaps
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theorems.Thm_Sensitivity213981Formal_CandidateCoherence_target_plus_high_cap
import Theorems.Thm_Sensitivity213981Formal_GuardAugmentation_target_plus_extra_high_cap


namespace Sensitivity213981Formal
section
/- All prefix-cap ingredients are consequences of actual failed-guard sets
and the separately proved labeling exclusions. -/


set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace ThreeBoundPrefixCaps
open scoped Classical BigOperators
open TournamentHighRows CandidateCoherence GuardAugmentation ResidualCaps
open MarkedCandidateCaps ThreeBoundMarkers
noncomputable section
variable {V X : Type} [Fintype V] [DecidableEq V]





theorem ordinary_prefix_cap (R : V → V → Prop) (hR : IsTournament R)
    (ell : V → V → Bool) (P : X → Prop) (children : V → Bool → X)
    (T H : Finset V) (color : V → Bool) (q a : ℕ)
    (hexcl : NoOrdinary R ell q a)
    (hpartner : ∀ w ∈ T, ∀ c : Bool, c ≠ color w → P (children w c))
    (hhigh : ∀ w ∈ H, ∀ c : Bool, P (children w c))
    (hT : ∀ v ∈ T, (guardFailures R ell P children v).card ≤  q) :
    T.card ≤  min (a-1-(outsideHigh R ell P children H T q).card)
      (a-(outsideHigh R ell P children H T (q+1)).card) := by
  have hsub (b : ℕ) : outsideHigh R ell P children H T b ⊆ H := by
    intro v hv
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hv).1).1
  have hdis (b : ℕ) : Disjoint T (outsideHigh R ell P children H T b) := by
    apply Finset.disjoint_left.mpr
    intro v hvT hvH
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hvH).1).2 hvT
  have hbudget (b : ℕ) : ∀ v ∈ outsideHigh R ell P children H T b,
      (guardFailures R ell P children v).card ≤  b :=
    fun _ hv => (Finset.mem_filter.mp hv).2
  have h₀ := target_plus_high_cap R ell P children T
    (outsideHigh R ell P children H T q) (hdis q) q a hexcl color hpartner
    (fun w hw => hhigh w (hsub q hw)) hT (hbudget q)
  have h₁ := target_plus_extra_high_cap R hR ell P children T
    (outsideHigh R ell P children H T (q+1)) (hdis (q+1)) q a hexcl color hpartner
    (fun w hw => hhigh w (hsub (q+1) hw)) hT (hbudget (q+1))
  omega







end
end ThreeBoundPrefixCaps






end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {V X : Type} [inst : Fintype.{0} V] [inst_1 : DecidableEq.{1} V] (R : V → V → Prop)
  (hR : @Sensitivity213981Formal.TournamentHighRows.IsTournament V R) (ell : V → V → Bool) (P : X → Prop)
  (children : V → Bool → X) (T H : Finset.{0} V) (color : V → Bool) (q a : Nat)
  (hexcl : @Sensitivity213981Formal.CandidateCoherence.NoOrdinary V R ell q a)
  (hpartner :
    ∀ (w : V),
      @Membership.mem.{0, 0} V (Finset.{0} V)
          (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) T w →
        ∀ (c : Bool), @Ne.{1} Bool c (color w) → P (children w c))
  (hhigh :
    ∀ (w : V),
      @Membership.mem.{0, 0} V (Finset.{0} V)
          (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H w →
        ∀ (c : Bool), P (children w c))
  (hT :
    ∀ (v : V),
      @Membership.mem.{0, 0} V (Finset.{0} V)
          (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) T v →
        @LE.le.{0} Nat instLENat
          (@Finset.card.{0} V (@Sensitivity213981Formal.TournamentHighRows.guardFailures V X inst R ell P children v))
          q),
  @LE.le.{0} Nat instLENat (@Finset.card.{0} V T)
    (@Min.min.{0} Nat instMinNat
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) a
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Finset.card.{0} V
          (@Sensitivity213981Formal.ThreeBoundPrefixCaps.outsideHigh V X inst inst_1 R ell P children H T q)))
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) a
        (@Finset.card.{0} V
          (@Sensitivity213981Formal.ThreeBoundPrefixCaps.outsideHigh V X inst inst_1 R ell P children H T
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) q
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))) := @Sensitivity213981Formal.ThreeBoundPrefixCaps.ordinary_prefix_cap
