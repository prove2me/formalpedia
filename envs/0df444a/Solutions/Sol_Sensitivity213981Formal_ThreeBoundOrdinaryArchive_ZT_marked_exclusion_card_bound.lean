-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZT.marked_exclusion_card_bound
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T18:49:29.771829+00:00
-- url     : https://prove2.me/submissions/17272c3a-b19c-41cd-85f4-1e74141faf25

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_Supplement_ArchivedOrdinaryDefinitions
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundOrdinaryArchive_ZL_markedGood_mono


namespace Sensitivity213981Formal
section
/- Adapted complete accepted Apache-2.0 Prove2me proofs by @yousofy. See ordinary_provenance.json. -/


open OAI.Paper320
namespace ThreeBoundOrdinaryArchive

/- selected_exists_labelCaps sections z8,z46 -/
set_option autoImplicit false
set_option Elab.async false
section z8

section

set_option maxHeartbeats 6000000
open scoped Classical BigOperators

namespace ZL
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]























end
end ZL
end
end z8

section z46

set_option maxHeartbeats 600000
open scoped Classical BigOperators
noncomputable section

namespace ZT
open OAI.Paper320 ZL SensitivityQ
variable {k : ℕ}



theorem marked_exclusion_card_bound (T : Tournament k)
    (label : Fin k → Fin k → Fin 2) (q a m B : ℕ)
    (h : ∀ I : MarkedIndex (Fin k) a m,
      ¬ (markedFamily T.Adj q a m B).bad I (fun e => label e.1 e.2)) :
    MarkedCardBound T label q m 0 B a := by
  intro A M P color hdis hPM hM hP hg
  have hpempty : P = ∅ := Finset.card_eq_zero.mp hP
  subst P
  by_contra hn
  obtain ⟨A',hA',hcard⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_gt hn)
  have hcompl : A' ⊆ Mᶜ := by
    intro x hx
    exact Finset.mem_compl.mpr (fun hm => Finset.disjoint_left.mp hdis (hA' hx) hm)
  let MI : (Finset.univ : Finset (Fin k)).powersetCard m :=
    ⟨M,Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hM⟩⟩
  let I : MarkedIndex (Fin k) a m :=
    ⟨MI,⟨A',Finset.mem_powersetCard.mpr ⟨hcompl,hcard⟩⟩⟩
  apply h I
  exact ⟨color,markedGood_mono T.Adj (fun e => label e.1 e.2)
    A A' M ∅ ∅ hA' (Finset.Subset.refl _) q B B le_rfl color hg⟩







end ZT
end
end z46


end ThreeBoundOrdinaryArchive

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {k : Nat} (T : Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320.Tournament k)
  (label : Fin k → Fin k → Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (q a m B : Nat)
  (h :
    ∀
      (I :
        @Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZL.MarkedIndex.{0} (Fin k) (Fin.fintype k)
          (instDecidableEqFin k) a m),
      Not
        (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZL.SupportedFamily.bad.{0, 0} (Prod.{0, 0} (Fin k) (Fin k))
          (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZL.MarkedIndex.{0} (Fin k) (Fin.fintype k)
            (instDecidableEqFin k) a m)
          (fun (a b : Prod.{0, 0} (Fin k) (Fin k)) =>
            @instDecidableEqProd.{0, 0} (Fin k) (Fin k) (instDecidableEqFin k) (instDecidableEqFin k) a b)
          (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZL.markedFamily.{0} (Fin k) (Fin.fintype k)
            (instDecidableEqFin k)
            (@Digraph.Adj.{0} (Fin k)
              (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320.Tournament.toDigraph k T))
            q a m B)
          I fun (e : Prod.{0, 0} (Fin k) (Fin k)) =>
          label (@Prod.fst.{0, 0} (Fin k) (Fin k) e) (@Prod.snd.{0, 0} (Fin k) (Fin k) e))),
  @Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZT.MarkedCardBound k T label q m
    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) B a := @Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZT.marked_exclusion_card_bound
